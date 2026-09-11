/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-!
# A BATCH of KEM / PKE / key-exchange protocols as axis-6 `ProtocolKernels` instances

This file instantiates the per-protocol emit-realization template
(`ProtocolEmitRealizes.ProtocolKernels` + `runRealizes`) on a **batch of real
KEM / PKE / key-exchange protocols**: ML-KEM (Kyber, FIPS 203), X25519 / ECDH
(RFC 7748 Montgomery ladder), and RSA-OAEP (RFC 8017).

Each protocol's emitted kernels chain as a **unary `state → state` pipeline**,
exactly the shape the `ProtocolKernels` template models — so each protocol's
*whole* emit-realization assembles from its per-kernel rows by one `runRealizes`
call, with no per-protocol proof skeleton.

* **ML-KEM (Kyber)** — its symmetric/sampling **spine** is a heterogeneous
  SHAKE / SHA-3 / rejection-sampling / compression chain (the Keccak-based
  steps): `sha3_512` key-derivation, `shake128` matrix-`A` expansion +
  `sample_ntt_poly` rejection sampling, `shake256` noise sampling, and the
  `compress`/`decompress` ciphertext coders.  We cite the registered Keccak /
  SHA-3 / SHAKE rows (`HashKernelRegistryEntry`,
  `KdfMacProtocolKernels.keccak_f1600`) for the leaf-names.  The NTT-multiply
  *arithmetic* of ML-KEM is **not** part of this unary spine: it is the
  registered **binary** NTT row `"ntt_poly_mul_3329_256"`
  (`KernelRealizesClass.nttMulC` / `GenericNttEmitValue.NttEmitRealizes`), linked
  in separately — `ProtocolKernels` is unary, so the symmetric/sampling spine and
  the binary NTT-multiply realization compose at the protocol level, not inside a
  single `pipeN`.

* **X25519 / ECDH** — the Montgomery ladder (RFC 7748) is a chain of `255`
  ladder-step folds, one `σ → σ` per scalar bit (each a constant-time
  conditional-swap + double-and-add).  This is the *pure n-fold* unary pipeline,
  parametric in the bit count (like HKDF's n-block expand).

* **RSA-OAEP** — the OAEP encode/decode (RFC 8017 §7.1) is an MGF1 mask chain:
  `mgf1_sha256` mask-generation blocks over the seed/DB, then the modular RSA
  permutation `rsa_apply_pk`.  This is the one-prefix-then-`n`-blocks chain
  (`n` MGF1 mask blocks, then the RSA permutation as the final fold).

## What each protocol delivers

For protocol `P`:

* `<P>Specs` — the kernel pipeline as a list of unary specs over a carrier `C`:
  **abstract** opaque `C → C` round functions.  The deliverable is the
  protocol-structure composition, not re-deriving the protocol's primitive
  internals.
* `<P>Leaves` — the matching emitted leaf-names, taken from the real extractions
  (`CatCrypt/Crypto/{MLKEM,X25519,RSAOAEP}/`) and the registered hash/Keccak rows.
* `<P>Protocol` — the assembled `ProtocolKernels C leafSpec`, whose `realized`
  field is the position-wise `List.Forall₂` of the per-kernel realizations, each
  taken as a **hypothesis** — exactly how a protocol cites each kernel's
  leaf-bytes KAT at instantiation.
* `<P>_protocol_realizes` — the whole-protocol emit-realization,
  `decode (pipeN <P>Leaves …) = composeSpecs <P>Specs (decode x)`, obtained by a
  single `runRealizes` call from the per-kernel realizations and the generic
  composition law.

## The point (axis-6 on a batch of KEM/PKE protocols)

These KEM/PKE/key-exchange protocols' *whole* emit-realizations assemble from
their hash / sample / ladder kernel rows by the generic template.  Per-protocol
emit is: list the kernels, cite each kernel's realization (the leaf-bytes KAT, an
honest hypothesis here), and apply `runRealizes`.  ML-KEM's NTT arithmetic is the
registered binary NTT row linked in separately; the unary pipeline here is the
symmetric/sampling spine.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.KemProtocolKernels

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

variable {C : Type*}

/-! ## §0  Shared pipeline assemblers

Three reusable unary-pipeline shapes cover all the protocols below:

* `heteroPipe` — a **heterogeneous** list of named kernel steps (leaf, spec) — the
  ML-KEM symmetric/sampling spine, whose leaves are distinct primitives
  (`sha3_512`, `shake128`, …).
* `foldPipe` — a **pure `n`-fold** of one block leaf, `n` copies of one step
  family indexed by position — the X25519 ladder (one step per bit).
* `chainPipe` — a **one-prefix-then-`n`-blocks** chain — RSA-OAEP (n MGF1 blocks
  then the RSA permutation), reusing the HKDF/KMAC chain shape.

Each comes with a `*Realized` `Forall₂`-assembly lemma and a `*Protocol` +
`*_realizes` pair, so each protocol instance is a thin renaming. -/

/-- A heterogeneous kernel pipeline: a list of `(leafName, stepSpec)` pairs, each
    a distinct primitive's leaf and its abstract unary spec. -/
def heteroLeaves (steps : List (String × (C → C))) : List String :=
  steps.map Prod.fst

/-- The matching spec list of a heterogeneous pipeline. -/
def heteroSpecs (steps : List (String × (C → C))) : List (C → C) :=
  steps.map Prod.snd

/-- The position-wise realization bundle for a heterogeneous pipeline: each pair's
    leaf realizes its spec.  Assembled by induction on the step list from the
    per-step realization hypotheses (`List.Forall`, one per registered row). -/
theorem heteroRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (steps : List (String × (C → C)))
    (hSteps : ∀ p ∈ steps, KernelRealizes decode p.2 p.1 leafSpec) :
    List.Forall₂
      (fun leaf spec => KernelRealizes decode spec leaf leafSpec)
      (heteroLeaves steps) (heteroSpecs steps) := by
  unfold heteroLeaves heteroSpecs
  induction steps with
  | nil => exact List.Forall₂.nil
  | cons p rest ih =>
      refine List.Forall₂.cons (hSteps p (List.mem_cons_self ..)) ?_
      exact ih (fun q hq => hSteps q (List.mem_cons_of_mem _ hq))

/-- The assembled heterogeneous `ProtocolKernels`. -/
def heteroProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (steps : List (String × (C → C)))
    (hSteps : ∀ p ∈ steps, KernelRealizes decode p.2 p.1 leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := heteroLeaves steps
  specs := heteroSpecs steps
  decode := decode
  realized := heteroRealized leafSpec decode steps hSteps

/-- The whole heterogeneous-pipeline emit-realization, by one `runRealizes`. -/
theorem hetero_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (steps : List (String × (C → C)))
    (hSteps : ∀ p ∈ steps, KernelRealizes decode p.2 p.1 leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (heteroLeaves steps) oldDest xVal)
      = composeSpecs (heteroSpecs steps) (decode xVal) :=
  (heteroProtocol leafSpec decode steps hSteps).runRealizes oldDest xVal

/-- A pure `n`-fold pipeline: `n` copies of one block leaf, with one step spec per
    position. -/
def foldLeaves (blockLeaf : String) (n : Nat) : List String :=
  List.replicate n blockLeaf

/-- The matching `n`-fold spec list: `blockStep 0, …, blockStep (n-1)`. -/
def foldSpecs (blockStep : Nat → C → C) (n : Nat) : List (C → C) :=
  (List.range n).map (fun i => blockStep i)

/-- The position-wise realization bundle for an `n`-fold pipeline, assembled by
    induction on `n` from one block realization per position. -/
theorem foldRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (blockStep : Nat → C → C) (blockLeaf : String) (n : Nat)
    (hBlock : ∀ i, KernelRealizes decode (blockStep i) blockLeaf leafSpec) :
    List.Forall₂
      (fun leaf spec => KernelRealizes decode spec leaf leafSpec)
      (foldLeaves blockLeaf n) (foldSpecs blockStep n) := by
  unfold foldLeaves foldSpecs
  induction n with
  | zero => exact List.Forall₂.nil
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.replicate_succ']
      exact List.rel_append ih (List.Forall₂.cons (hBlock m) List.Forall₂.nil)

/-- The assembled `n`-fold `ProtocolKernels`. -/
def foldProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (blockStep : Nat → C → C) (blockLeaf : String) (n : Nat)
    (hBlock : ∀ i, KernelRealizes decode (blockStep i) blockLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := foldLeaves blockLeaf n
  specs := foldSpecs blockStep n
  decode := decode
  realized := foldRealized leafSpec decode blockStep blockLeaf n hBlock

/-- The whole `n`-fold pipeline emit-realization, by one `runRealizes`. -/
theorem fold_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (blockStep : Nat → C → C) (blockLeaf : String) (n : Nat)
    (hBlock : ∀ i, KernelRealizes decode (blockStep i) blockLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (foldLeaves blockLeaf n) oldDest xVal)
      = composeSpecs (foldSpecs blockStep n) (decode xVal) :=
  (foldProtocol leafSpec decode blockStep blockLeaf n hBlock).runRealizes oldDest xVal

/-- A `n`-blocks-then-suffix chain: `n` copies of a block leaf followed by one
    *suffix* kernel.  (The mirror of HKDF's prefix-then-blocks; here the
    distinguished kernel is the trailing one.) -/
def blocksThenSuffixLeaves (blockLeaf suffixLeaf : String) (n : Nat) : List String :=
  List.replicate n blockLeaf ++ [suffixLeaf]

/-- The matching spec list: `n` block specs then the suffix spec. -/
def blocksThenSuffixSpecs (blockStep : Nat → C → C) (suffixStep : C → C) (n : Nat) :
    List (C → C) :=
  (List.range n).map (fun i => blockStep i) ++ [suffixStep]

/-- The position-wise realization bundle for a blocks-then-suffix chain. -/
theorem blocksThenSuffixRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (blockStep : Nat → C → C) (suffixStep : C → C)
    (blockLeaf suffixLeaf : String) (n : Nat)
    (hBlock : ∀ i, KernelRealizes decode (blockStep i) blockLeaf leafSpec)
    (hSuffix : KernelRealizes decode suffixStep suffixLeaf leafSpec) :
    List.Forall₂
      (fun leaf spec => KernelRealizes decode spec leaf leafSpec)
      (blocksThenSuffixLeaves blockLeaf suffixLeaf n)
      (blocksThenSuffixSpecs blockStep suffixStep n) := by
  unfold blocksThenSuffixLeaves blocksThenSuffixSpecs
  exact List.rel_append
    (foldRealized leafSpec decode blockStep blockLeaf n hBlock)
    (List.Forall₂.cons hSuffix List.Forall₂.nil)

/-- The assembled blocks-then-suffix `ProtocolKernels`. -/
def blocksThenSuffixProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (blockStep : Nat → C → C) (suffixStep : C → C)
    (blockLeaf suffixLeaf : String) (n : Nat)
    (hBlock : ∀ i, KernelRealizes decode (blockStep i) blockLeaf leafSpec)
    (hSuffix : KernelRealizes decode suffixStep suffixLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := blocksThenSuffixLeaves blockLeaf suffixLeaf n
  specs := blocksThenSuffixSpecs blockStep suffixStep n
  decode := decode
  realized :=
    blocksThenSuffixRealized leafSpec decode blockStep suffixStep
      blockLeaf suffixLeaf n hBlock hSuffix

/-- The whole blocks-then-suffix emit-realization, by one `runRealizes`. -/
theorem blocksThenSuffix_protocol_realizes (leafSpec : LeafSpec)
    (decode : RustVal .TFp → C)
    (blockStep : Nat → C → C) (suffixStep : C → C)
    (blockLeaf suffixLeaf : String) (n : Nat)
    (hBlock : ∀ i, KernelRealizes decode (blockStep i) blockLeaf leafSpec)
    (hSuffix : KernelRealizes decode suffixStep suffixLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (blocksThenSuffixLeaves blockLeaf suffixLeaf n)
        oldDest xVal)
      = composeSpecs (blocksThenSuffixSpecs blockStep suffixStep n) (decode xVal) :=
  (blocksThenSuffixProtocol leafSpec decode blockStep suffixStep
    blockLeaf suffixLeaf n hBlock hSuffix).runRealizes oldDest xVal

/-! ## §1  ML-KEM (Kyber, FIPS 203) — the symmetric/sampling spine

ML-KEM's encaps/decaps is built on a Keccak-based **symmetric spine**: a
`sha3_512` key/coin-derivation, a `shake128`-driven matrix-`A` expansion feeding
a `sample_ntt_poly` rejection-sampler, a `shake256` noise sampler, and the
`compress`/`decompress` ciphertext coders.  Each is a unary `state → state` step
over the running KEM state, so the spine is exactly the heterogeneous `pipeN` the
template threads.

Leaf-names from the real extraction (`CatCrypt/Crypto/MLKEM/Extraction/`,
`MlkemLowCT.lean`) and the registered Keccak/SHAKE rows:
`"sha3_512"`, `"shake128"`, `"sample_ntt_poly"`, `"shake256"`,
`"compress_coeff"`, `"decompress_coeff"`.

**The NTT-multiply arithmetic is NOT in this spine.**  ML-KEM's polynomial
products are the registered **binary** NTT row `"ntt_poly_mul_3329_256"`
(`KernelRealizesClass.nttMulC` / `GenericNttEmitValue.NttEmitRealizes`, with the
unconditional cyclic realizer `ConcreteNttRealizer.mlkem_nttEmitRealizes_concrete`).
`ProtocolKernels` is a *unary* template (one output feeds one input), whereas
NTT-multiply takes two polynomial operands; so the binary NTT realization is
linked in separately and composes with this symmetric/sampling spine at the
protocol level — it is not part of `mlkemSpineSpecs`. -/

/-- ML-KEM `sha3_512` key/coin-derivation leaf (FIPS 203 `G`). -/
def mlkemSha3_512Leaf : String := "sha3_512"

/-- ML-KEM `shake128` matrix-`A` expansion leaf (XOF, FIPS 203 §4.2.2). -/
def mlkemShake128Leaf : String := "shake128"

/-- ML-KEM rejection-sampling-from-XOF leaf (`SampleNTT`, FIPS 203 Alg. 7). -/
def mlkemSampleNttLeaf : String := "sample_ntt_poly"

/-- ML-KEM `shake256` CBD-noise sampler leaf (FIPS 203 §4.2.2 `PRF`). -/
def mlkemShake256Leaf : String := "shake256"

/-- ML-KEM coefficient-compression coder leaf (FIPS 203 §4.2.1). -/
def mlkemCompressLeaf : String := "compress_coeff"

/-- ML-KEM coefficient-decompression coder leaf (FIPS 203 §4.2.1). -/
def mlkemDecompressLeaf : String := "decompress_coeff"

/-- The ML-KEM symmetric/sampling **spine** as a heterogeneous step list (leaf,
    abstract unary spec): `G` key-derivation, `shake128` `A`-expansion,
    `SampleNTT` rejection sampler, `shake256` noise sampler, then the
    compress/decompress coders.  These are abstract opaque `C → C` round
    functions; the deliverable is the spine composition, not re-deriving Keccak. -/
def mlkemSpineSteps
    (gStep aExpandStep sampleStep noiseStep compressStep decompressStep : C → C) :
    List (String × (C → C)) :=
  [ (mlkemSha3_512Leaf, gStep),
    (mlkemShake128Leaf, aExpandStep),
    (mlkemSampleNttLeaf, sampleStep),
    (mlkemShake256Leaf, noiseStep),
    (mlkemCompressLeaf, compressStep),
    (mlkemDecompressLeaf, decompressStep) ]

/-- The ML-KEM spine leaf list. -/
def mlkemSpineLeaves
    (gStep aExpandStep sampleStep noiseStep compressStep decompressStep : C → C) :
    List String :=
  heteroLeaves (mlkemSpineSteps gStep aExpandStep sampleStep noiseStep
    compressStep decompressStep)

/-- The ML-KEM spine spec list. -/
def mlkemSpineSpecs
    (gStep aExpandStep sampleStep noiseStep compressStep decompressStep : C → C) :
    List (C → C) :=
  heteroSpecs (mlkemSpineSteps gStep aExpandStep sampleStep noiseStep
    compressStep decompressStep)

/-- **The assembled ML-KEM symmetric/sampling spine protocol.**  Each spine leaf
    realizes its abstract step (each an honest leaf-bytes KAT hypothesis — the
    registered Keccak / SHAKE / SHA-3 rows), assembled by `heteroRealized`.  The
    binary NTT-multiply row `"ntt_poly_mul_3329_256"` is linked separately. -/
def mlkemProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (gStep aExpandStep sampleStep noiseStep compressStep decompressStep : C → C)
    (hG : KernelRealizes decode gStep mlkemSha3_512Leaf leafSpec)
    (hA : KernelRealizes decode aExpandStep mlkemShake128Leaf leafSpec)
    (hSample : KernelRealizes decode sampleStep mlkemSampleNttLeaf leafSpec)
    (hNoise : KernelRealizes decode noiseStep mlkemShake256Leaf leafSpec)
    (hCompress : KernelRealizes decode compressStep mlkemCompressLeaf leafSpec)
    (hDecompress : KernelRealizes decode decompressStep mlkemDecompressLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  heteroProtocol leafSpec decode
    (mlkemSpineSteps gStep aExpandStep sampleStep noiseStep compressStep decompressStep)
    (by
      intro p hp
      simp only [mlkemSpineSteps, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with h | h | h | h | h | h <;> subst h <;>
        simp only [] <;>
        first
          | exact hG | exact hA | exact hSample
          | exact hNoise | exact hCompress | exact hDecompress)

/-- **The whole ML-KEM symmetric/sampling-spine emit-realization (axis-6).**  The
    full `sha3_512`→`shake128`→`SampleNTT`→`shake256`→compress→decompress `pipeN`
    spine, read through `decode`, computes the composite
    `composeSpecs (mlkemSpineSpecs …)` of the input.  A single `runRealizes` call
    from the per-kernel realizations (each citing a registered Keccak/SHAKE/SHA-3
    row) and the generic composition law.

    The NTT-multiply arithmetic is the registered binary row
    `"ntt_poly_mul_3329_256"` (`KernelRealizesClass.nttMulC`), linked in
    separately — it is binary, not part of this unary spine. -/
theorem mlkem_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (gStep aExpandStep sampleStep noiseStep compressStep decompressStep : C → C)
    (hG : KernelRealizes decode gStep mlkemSha3_512Leaf leafSpec)
    (hA : KernelRealizes decode aExpandStep mlkemShake128Leaf leafSpec)
    (hSample : KernelRealizes decode sampleStep mlkemSampleNttLeaf leafSpec)
    (hNoise : KernelRealizes decode noiseStep mlkemShake256Leaf leafSpec)
    (hCompress : KernelRealizes decode compressStep mlkemCompressLeaf leafSpec)
    (hDecompress : KernelRealizes decode decompressStep mlkemDecompressLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec
        (mlkemSpineLeaves gStep aExpandStep sampleStep noiseStep
          compressStep decompressStep) oldDest xVal)
      = composeSpecs
          (mlkemSpineSpecs gStep aExpandStep sampleStep noiseStep
            compressStep decompressStep) (decode xVal) :=
  (mlkemProtocol leafSpec decode gStep aExpandStep sampleStep noiseStep
    compressStep decompressStep hG hA hSample hNoise hCompress hDecompress).runRealizes
    oldDest xVal

/-! ## §2  X25519 / ECDH — the Montgomery ladder (RFC 7748)

X25519 computes a scalar multiple on Curve25519 by the **Montgomery ladder**: for
each of the `255` scalar bits, one constant-time `ladder_step` (a conditional
swap `cswap` then a double-and-add over the projective `(X, Z)` state) advances
the running ladder state `σ`.  The whole scalar multiplication is therefore a
*pure `n`-fold* of one `ladder_step` leaf — the `foldPipe` unary pipeline,
parametric in the bit count `n` (`n = 255` for Curve25519).

The ladder field arithmetic is the emitted Curve25519 field kernel
(`CatCrypt/Crypto/X25519/EmittedFieldRealization.lean`'s `feLadderStep`); the
ladder-step leaf is its emitted name.  Each step's spec is a distinct abstract
`C → C` (the bit-`i` ladder transition), all realized by the one
`ladder_step` kernel. -/

/-- The emitted X25519 Montgomery-ladder step kernel leaf (RFC 7748 §5,
    `EmittedFieldRealization.feLadderStep`: `cswap` + double-and-add). -/
def x25519LadderStepLeaf : String := "x25519_ladder_step"

/-- The X25519 leaf list: `n` copies of the ladder-step leaf (`n = 255` for
    Curve25519). -/
def x25519Leaves (n : Nat) : List String :=
  foldLeaves x25519LadderStepLeaf n

/-- The X25519 kernel-spec list: the per-bit ladder transitions
    `ladderStep 0, …, ladderStep (n-1)`. -/
def x25519Specs (ladderStep : Nat → C → C) (n : Nat) : List (C → C) :=
  foldSpecs ladderStep n

/-- **The assembled X25519 protocol.**  `n` Montgomery-ladder steps, their
    abstract per-bit transition specs, the decoder, and the per-step realizations
    (each an honest leaf-bytes KAT hypothesis on the one `ladder_step` kernel)
    assembled by `foldRealized`. -/
def x25519Protocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (ladderStep : Nat → C → C) (n : Nat)
    (hLadder : ∀ i, KernelRealizes decode (ladderStep i) x25519LadderStepLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  foldProtocol leafSpec decode ladderStep x25519LadderStepLeaf n hLadder

/-- **The whole X25519 / ECDH emit-realization (axis-6).**  The full `n`-step
    Montgomery-ladder `pipeN` pipeline (`n = 255` for Curve25519), read through
    `decode`, computes the composite `composeSpecs (x25519Specs …)` of the input
    point.  A single `runRealizes` call from the per-step realizations and the
    generic composition law. -/
theorem x25519_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (ladderStep : Nat → C → C) (n : Nat)
    (hLadder : ∀ i, KernelRealizes decode (ladderStep i) x25519LadderStepLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (x25519Leaves n) oldDest xVal)
      = composeSpecs (x25519Specs ladderStep n) (decode xVal) :=
  (x25519Protocol leafSpec decode ladderStep n hLadder).runRealizes oldDest xVal

/-! ## §3  RSA-OAEP (RFC 8017 §7.1)

RSA-OAEP encryption masks the seed/data block with **MGF1** (a SHA-256-driven
mask-generation chain) and then applies the RSA public-key permutation.  In
emit-pipeline order: `n` `mgf1_sha256` mask-generation blocks fold over the
running OAEP buffer, then the modular RSA permutation `rsa_apply_pk` is the final
fold.  This is the *blocks-then-suffix* unary chain — `n` MGF1 mask blocks then
one RSA-permutation suffix.

Leaf-names from the real extraction (`CatCrypt/Crypto/RSAOAEP/Extraction/`):
`"mgf1_sha256"` (the MGF1 mask block, itself an emitted SHA-256 chain) and
`"rsa_apply_pk"` (the modular-exponentiation public-key permutation). -/

/-- The RSA-OAEP MGF1 mask-generation block leaf (RFC 8017 §B.2.1, SHA-256). -/
def rsaOaepMgf1Leaf : String := "mgf1_sha256"

/-- The RSA-OAEP public-key (modular-exponentiation) permutation leaf
    (RFC 8017 §5.1.1 `RSAEP`). -/
def rsaOaepApplyPkLeaf : String := "rsa_apply_pk"

/-- The RSA-OAEP leaf list: `n` MGF1 mask blocks then the RSA permutation. -/
def rsaOaepLeaves (n : Nat) : List String :=
  blocksThenSuffixLeaves rsaOaepMgf1Leaf rsaOaepApplyPkLeaf n

/-- The RSA-OAEP kernel-spec list: `n` MGF1 mask-fold specs then the RSA
    permutation spec. -/
def rsaOaepSpecs (mgf1Step : Nat → C → C) (rsaStep : C → C) (n : Nat) :
    List (C → C) :=
  blocksThenSuffixSpecs mgf1Step rsaStep n

/-- **The assembled RSA-OAEP protocol.**  `n` MGF1 mask blocks then the RSA
    permutation, their abstract step specs, the decoder, and the per-kernel
    realizations (each an honest leaf-bytes KAT hypothesis) assembled by
    `blocksThenSuffixRealized`. -/
def rsaOaepProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (mgf1Step : Nat → C → C) (rsaStep : C → C) (n : Nat)
    (hMgf1 : ∀ i, KernelRealizes decode (mgf1Step i) rsaOaepMgf1Leaf leafSpec)
    (hRsa : KernelRealizes decode rsaStep rsaOaepApplyPkLeaf leafSpec) :
    ProtocolKernels C leafSpec :=
  blocksThenSuffixProtocol leafSpec decode mgf1Step rsaStep
    rsaOaepMgf1Leaf rsaOaepApplyPkLeaf n hMgf1 hRsa

/-- **The whole RSA-OAEP emit-realization (axis-6).**  The full `n`-block MGF1
    mask chain then RSA-permutation `pipeN` pipeline, read through `decode`,
    computes the composite `composeSpecs (rsaOaepSpecs …)` of the input.  A single
    `runRealizes` call from the per-kernel realizations and the generic
    composition law. -/
theorem rsaOaep_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (mgf1Step : Nat → C → C) (rsaStep : C → C) (n : Nat)
    (hMgf1 : ∀ i, KernelRealizes decode (mgf1Step i) rsaOaepMgf1Leaf leafSpec)
    (hRsa : KernelRealizes decode rsaStep rsaOaepApplyPkLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (rsaOaepLeaves n) oldDest xVal)
      = composeSpecs (rsaOaepSpecs mgf1Step rsaStep n) (decode xVal) :=
  (rsaOaepProtocol leafSpec decode mgf1Step rsaStep n hMgf1 hRsa).runRealizes
    oldDest xVal

end CatCrypt.Crypto.SecureCompilation.KemProtocolKernels
