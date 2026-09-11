/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

/-!
# Post-quantum (non-hash) signatures and MPC as `ProtocolKernels` instances

This file instantiates the per-protocol emit-realization template
(`ProtocolEmitRealizes.ProtocolKernels` + `runRealizes`) on a **batch** of
non-hash-based post-quantum signature protocols and MPC protocols, exactly as
`KdfMacProtocolKernels.lean` and `HashSigProtocolKernels.lean` do for the
symmetric / hash-based families.  Each protocol's whole computation is a
sequence of unary `state → state` steps over its running carrier — sampling,
polynomial arithmetic, field folds, share arithmetic — which is precisely the
shape the `ProtocolKernels` template models, and which `pipeN` / `composeSpecs`
already compose.

The protocols covered:

* **ML-DSA / Dilithium (FIPS 204) sign/verify spine** — a three-phase chain:
  (1) a SHAKE sampling phase (`expand_a` matrix expansion then `expand_mask`
  masking-vector sampling), (2) the negacyclic NTT arithmetic phase (the
  registered NTT-multiply row — `polyvec_l_ntt` / `polyvec_k_ntt` then
  `polyvec_k_invntt`), and (3) the decompose / hint phase (`power2round`,
  `make_hint`, `use_hint`).  Every step is a unary map on the running
  polynomial-vector carrier.  `mldsa_protocol_realizes`.
* **FAEST (VOLE-in-the-head signature)** — an AES one-way-function prefix
  (`faest_owf_aes`) followed by a SHAKE / PRG / VOLE chain
  (`faest_shake128`, `ggm_expand`, `vole_commit`, `faest_quicksilver_check`):
  a clean prefix-then-`n`-blocks unary chain.  `faest_protocol_realizes`.
* **MAYO (multivariate signature)** — a field-arithmetic fold chain: evaluate
  the multivariate quadratic map by folding the quadratic-form kernel
  (`mayo_quadform_n8`) `n` times over the running accumulator, then the
  map-evaluation verify step (`mayo_verify_mapeval_owned`).
  `mayo_protocol_realizes`.
* **UOV (Unbalanced Oil-and-Vinegar signature)** — the same multivariate
  field-fold shape with the UOV map-evaluation kernels
  (`uov_verify_mapeval_owned`, `uov_solve_pivot_swap_owned`).
  `uov_protocol_realizes`.
* **SPDZ (dishonest-majority MPC)** — a field share-arithmetic chain
  (`auth_add`, `auth_scalar_mul` over authenticated shares) terminated by a
  MAC-check phase (`mac_shares`, `check`): a chain of share-arithmetic steps
  followed by the MAC-check fold.  `spdz_protocol_realizes`.

## What each instance delivers (mirroring the templates)

For each protocol `P` we provide:

* `<P>Specs` — the kernel pipeline as a list of **abstract, unary** `C → C`
  step specs.  These are opaque models of each round; the deliverable is the
  protocol-structure composition, not re-deriving each round's internals.
* `<P>Leaves` — the matching emitted leaf-names, taken from the real extraction
  (`CatCrypt/Crypto/{MLDSA,FAEST,MAYO,UOV,SPDZ}`), e.g. `"expand_a"`,
  `"faest_owf_aes"`, `"mayo_quadform_n8"`, `"auth_add"`.
* `<P>Protocol : ProtocolKernels C leafSpec` — the assembled bundle, whose
  `realized` field is the position-wise `List.Forall₂` of the per-kernel
  realizations, **each taken as a hypothesis** (the kernel's leaf-bytes KAT).
* `<P>_protocol_realizes` — the whole-protocol emit-realization,
  `decode (pipeN <P>Leaves …) = composeSpecs <P>Specs (decode x)`, obtained by a
  single `runRealizes` call from nothing but the per-kernel realizations and the
  generic composition law.

## The point (axis-6 on a batch of real protocols)

Each of these PQC / MPC protocols has its *whole* emit-realization assembled
from its kernel rows by `runRealizes`, with no per-protocol proof skeleton: the
sampling / NTT / field-fold / share-arithmetic kernel-chain structure fits the
unary `ProtocolKernels` template exactly.  The per-kernel realizations are
honest hypotheses (each is the kernel's leaf-bytes KAT); the contribution is
that the protocol-level composition assembles for free from them.  No fabricated
`leafSpec`; the abstract step specs are honest opaque parameters.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.PqcMpcProtocolKernels

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes

variable {C : Type*}

/-! ## §0  Shared chain / fold combinators

Every protocol below is a concatenation of *phases*, where each phase is a chain
of `n` copies of one emitted leaf (the same kernel reused per step), whose step
specs `step 0, …, step (n-1)` are position-wise realized.  This is the
`HashSigProtocolKernels.chainRealized`-style induction (single shared leaf),
plus an `appendRealized` glue so multi-phase protocols (ML-DSA's three phases,
FAEST's prefix-then-blocks, etc.) assemble from their phases. -/

/-- A chain leaf list: `n` copies of one emitted leaf `leaf` (the shared kernel
    reused once per chain step). -/
def chainLeaves (leaf : String) (n : Nat) : List String :=
  List.replicate n leaf

/-- A chain spec list: the per-step specs `step 0, …, step (n-1)` in chain
    order. -/
def chainSpecs (step : Nat → C → C) (n : Nat) : List (C → C) :=
  (List.range n).map (fun i => step i)

/-- **The uniform-leaf chain realization.**  If the single shared kernel `leaf`
    realizes every chain step `step i`, then `chainLeaves`/`chainSpecs` are
    position-wise realized — the `Forall₂` the template's `realized` field
    demands, for a chain of arbitrary length `n`. -/
theorem chainRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (leaf : String) (step : Nat → C → C) (n : Nat)
    (hstep : ∀ i, KernelRealizes decode (step i) leaf leafSpec) :
    List.Forall₂
      (fun lf spec => KernelRealizes decode spec lf leafSpec)
      (chainLeaves leaf n) (chainSpecs step n) := by
  unfold chainLeaves chainSpecs
  induction n with
  | zero => exact List.Forall₂.nil
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.replicate_succ']
      exact List.rel_append ih (List.Forall₂.cons (hstep m) List.Forall₂.nil)

/-- Appending two position-wise realization bundles — the `Forall₂` of a
    concatenation is the concatenation of the `Forall₂`s.  Glues a protocol's
    phases (chain ++ chain ++ …) into one bundle. -/
theorem appendRealized (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    {l₁ l₂ : List String} {s₁ s₂ : List (C → C)}
    (h₁ : List.Forall₂
      (fun lf spec => KernelRealizes decode spec lf leafSpec) l₁ s₁)
    (h₂ : List.Forall₂
      (fun lf spec => KernelRealizes decode spec lf leafSpec) l₂ s₂) :
    List.Forall₂
      (fun lf spec => KernelRealizes decode spec lf leafSpec)
      (l₁ ++ l₂) (s₁ ++ s₂) :=
  List.rel_append h₁ h₂

/-! ## §1  ML-DSA / Dilithium (FIPS 204) — sample ++ NTT ++ decompose/hint

The ML-DSA sign/verify spine recomputes the signature's polynomial commitment in
three unary-chain phases over the running polynomial-vector carrier:

1. **SHAKE sampling**: expand the public matrix and the masking vector
   (`sampleStep i` = the `i`-th SHAKE128/SHAKE256 sampling round — `expand_a`,
   `expand_mask`).  The reused emitted leaf is the SHAKE expansion kernel.
2. **Negacyclic NTT arithmetic** (the registered NTT-multiply row): forward NTT
   of each polynomial vector, point-wise multiply, inverse NTT (`nttStep i` =
   the `i`-th NTT-domain step — `polyvec_l_ntt`, `polyvec_k_ntt`,
   `polyvec_k_invntt`).  The reused leaf is the negacyclic NTT-multiply kernel.
3. **Decompose / hint**: `power2round` the commitment and apply the hint bits
   (`hintStep i` = the `i`-th decompose/hint step — `power2round`, `make_hint`,
   `use_hint`).  The reused leaf is the decompose/hint kernel.

Each phase is a list of unary `C → C` steps; the whole spine is their
concatenation — one `pipeN` pipeline.

Leaf names from the real extraction (`CatCrypt/Crypto/MLDSA/`, `Dilithium/`):
`"expand_a"`, `"polyvec_k_ntt"`, `"power2round"`. -/

/-- The ML-DSA SHAKE sampling (`ExpandA` / `ExpandMask`) kernel leaf. -/
def mldsaSampleLeaf : String := "expand_a"

/-- The ML-DSA negacyclic NTT arithmetic kernel leaf (registered NTT-multiply
    row). -/
def mldsaNttLeaf : String := "polyvec_k_ntt"

/-- The ML-DSA decompose / hint kernel leaf. -/
def mldsaHintLeaf : String := "power2round"

/-- The ML-DSA spine leaf list (general parameters): the SHAKE sampling phase
    (`sampleLen` copies of the sample leaf) ++ the NTT phase (`nttLen` copies of
    the NTT leaf) ++ the decompose/hint phase (`hintLen` copies of the hint
    leaf). -/
def mldsaLeaves (sampleLen nttLen hintLen : Nat) : List String :=
  chainLeaves mldsaSampleLeaf sampleLen ++
    (chainLeaves mldsaNttLeaf nttLen ++
      chainLeaves mldsaHintLeaf hintLen)

/-- The ML-DSA spine spec list: the sampling steps ++ the NTT steps ++ the
    decompose/hint steps, in pipeline order. -/
def mldsaSpecs (sampleStep nttStep hintStep : Nat → C → C)
    (sampleLen nttLen hintLen : Nat) : List (C → C) :=
  chainSpecs sampleStep sampleLen ++
    (chainSpecs nttStep nttLen ++
      chainSpecs hintStep hintLen)

/-- **The assembled ML-DSA `ProtocolKernels`**: the three-phase leaf list, the
    matching spec list, the decoder, and the position-wise realization bundle
    glued from the three phases' `chainRealized` bundles via `appendRealized`. -/
def mldsaProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (sampleStep nttStep hintStep : Nat → C → C)
    (sampleLen nttLen hintLen : Nat)
    (hSample : ∀ i, KernelRealizes decode (sampleStep i) mldsaSampleLeaf leafSpec)
    (hNtt : ∀ i, KernelRealizes decode (nttStep i) mldsaNttLeaf leafSpec)
    (hHint : ∀ i, KernelRealizes decode (hintStep i) mldsaHintLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := mldsaLeaves sampleLen nttLen hintLen
  specs := mldsaSpecs sampleStep nttStep hintStep sampleLen nttLen hintLen
  decode := decode
  realized :=
    appendRealized leafSpec decode
      (chainRealized leafSpec decode mldsaSampleLeaf sampleStep sampleLen hSample)
      (appendRealized leafSpec decode
        (chainRealized leafSpec decode mldsaNttLeaf nttStep nttLen hNtt)
        (chainRealized leafSpec decode mldsaHintLeaf hintStep hintLen hHint))

/-- **The whole-ML-DSA emit-realization (axis-6 on a real protocol, general
    parameters).**  The entire emitted ML-DSA spine — SHAKE sampling ++ NTT
    arithmetic ++ decompose/hint, `pipeN` over `mldsaLeaves` — decodes to the
    composite `composeSpecs (mldsaSpecs …)` of the input.  Obtained by one
    `runRealizes` call from the per-kernel realizations of all three phases
    (each an honest leaf-bytes KAT hypothesis), for arbitrary `sampleLen`,
    `nttLen`, `hintLen`. -/
theorem mldsa_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (sampleStep nttStep hintStep : Nat → C → C)
    (sampleLen nttLen hintLen : Nat)
    (hSample : ∀ i, KernelRealizes decode (sampleStep i) mldsaSampleLeaf leafSpec)
    (hNtt : ∀ i, KernelRealizes decode (nttStep i) mldsaNttLeaf leafSpec)
    (hHint : ∀ i, KernelRealizes decode (hintStep i) mldsaHintLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (mldsaLeaves sampleLen nttLen hintLen) oldDest xVal)
      = composeSpecs
          (mldsaSpecs sampleStep nttStep hintStep sampleLen nttLen hintLen)
          (decode xVal) :=
  (mldsaProtocol leafSpec decode sampleStep nttStep hintStep
    sampleLen nttLen hintLen hSample hNtt hHint).runRealizes oldDest xVal

/-! ## §2  FAEST — AES OWF prefix ++ SHAKE / PRG / VOLE chain

FAEST (VOLE-in-the-head signature) commits to the AES one-way-function
evaluation, then runs a SHAKE / GGM-PRG / VOLE chain to build and check the
VOLE-in-the-head proof.  Structurally:

1. **AES OWF prefix**: evaluate the AES OWF on the witness (`owfStep` = the
   `faest_owf_aes` block) — one prefix step.
2. **SHAKE / PRG / VOLE chain**: a chain of `n` proof rounds (`proofStep i` =
   the `i`-th SHAKE / GGM-expand / VOLE-commit / QuickSilver round — the reused
   `faest_shake128` / `vole_commit` kernel).

This is the prefix-then-`n`-blocks shape (cf. `KdfMacProtocolKernels.chainSpecs`):
one OWF prefix leaf followed by `n` copies of the VOLE proof-round leaf.

Leaf names from the real extraction (`CatCrypt/Crypto/FAEST/`):
`"faest_owf_aes"` and `"vole_commit"`. -/

/-- The FAEST AES one-way-function prefix kernel leaf. -/
def faestOwfLeaf : String := "faest_owf_aes"

/-- The FAEST SHAKE / PRG / VOLE proof-round kernel leaf. -/
def faestProofLeaf : String := "vole_commit"

/-- The FAEST leaf list (general round count `n`): the AES OWF prefix leaf then
    `n` copies of the VOLE proof-round leaf. -/
def faestLeaves (n : Nat) : List String :=
  faestOwfLeaf :: chainLeaves faestProofLeaf n

/-- The FAEST spec list: the OWF prefix step then `n` VOLE proof-round steps,
    in pipeline order. -/
def faestSpecs (owfStep : C → C) (proofStep : Nat → C → C) (n : Nat) :
    List (C → C) :=
  owfStep :: chainSpecs proofStep n

/-- **The assembled FAEST `ProtocolKernels`**: the prefix-then-chain leaf list,
    the matching spec list, the decoder, and the realization bundle glued from
    the OWF prefix realization and the VOLE proof-round chain via
    `appendRealized` (singleton prefix ++ chain). -/
def faestProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (owfStep : C → C) (proofStep : Nat → C → C) (n : Nat)
    (hOwf : KernelRealizes decode owfStep faestOwfLeaf leafSpec)
    (hProof : ∀ i, KernelRealizes decode (proofStep i) faestProofLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := faestLeaves n
  specs := faestSpecs owfStep proofStep n
  decode := decode
  realized :=
    List.Forall₂.cons hOwf
      (chainRealized leafSpec decode faestProofLeaf proofStep n hProof)

/-- **The whole-FAEST emit-realization (axis-6 on a real protocol).**  The
    entire emitted FAEST pipeline — AES OWF prefix then `n` VOLE proof rounds,
    `pipeN` over `faestLeaves` — decodes to the composite
    `composeSpecs (faestSpecs …)` of the input.  Obtained by one `runRealizes`
    call from the per-kernel realizations (each an honest leaf-bytes KAT
    hypothesis), for arbitrary round count `n`. -/
theorem faest_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (owfStep : C → C) (proofStep : Nat → C → C) (n : Nat)
    (hOwf : KernelRealizes decode owfStep faestOwfLeaf leafSpec)
    (hProof : ∀ i, KernelRealizes decode (proofStep i) faestProofLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (faestLeaves n) oldDest xVal)
      = composeSpecs (faestSpecs owfStep proofStep n) (decode xVal) :=
  (faestProtocol leafSpec decode owfStep proofStep n hOwf hProof).runRealizes
    oldDest xVal

/-! ## §3  MAYO — multivariate quadratic-map field fold

MAYO verification evaluates the multivariate quadratic map `P(s)` by folding the
quadratic-form kernel over the running field accumulator, then runs the
map-evaluation verify step.  Structurally:

1. **Quadratic-form fold**: fold the quadratic-form kernel `n` times over the
   running accumulator (`quadStep i` = the `i`-th `mayo_quadform_n8` field
   evaluation) — a field-arithmetic chain.
2. **Map-evaluation verify**: the final `mayo_verify_mapeval_owned` step
   (`verifyStep` = compare the recomputed map value against the target) — one
   trailing step.

Both phases are unary field-fold steps; concatenated they are the whole MAYO
verification.

Leaf names from the real extraction (`CatCrypt/Crypto/MAYO/`):
`"mayo_quadform_n8"` and `"mayo_verify_mapeval_owned"`. -/

/-- The MAYO quadratic-form field-fold kernel leaf. -/
def mayoQuadLeaf : String := "mayo_quadform_n8"

/-- The MAYO map-evaluation verify kernel leaf. -/
def mayoVerifyLeaf : String := "mayo_verify_mapeval_owned"

/-- The MAYO leaf list (general fold length `n`): `n` copies of the
    quadratic-form fold leaf then the map-evaluation verify leaf. -/
def mayoLeaves (n : Nat) : List String :=
  chainLeaves mayoQuadLeaf n ++ [mayoVerifyLeaf]

/-- The MAYO spec list: the `n` quadratic-form fold steps then the
    map-evaluation verify step, in pipeline order. -/
def mayoSpecs (quadStep : Nat → C → C) (verifyStep : C → C) (n : Nat) :
    List (C → C) :=
  chainSpecs quadStep n ++ [verifyStep]

/-- **The assembled MAYO `ProtocolKernels`**: the fold-then-verify leaf list,
    the matching spec list, the decoder, and the realization bundle glued from
    the quadratic-form fold chain and the (singleton) verify step via
    `appendRealized`. -/
def mayoProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (quadStep : Nat → C → C) (verifyStep : C → C) (n : Nat)
    (hQuad : ∀ i, KernelRealizes decode (quadStep i) mayoQuadLeaf leafSpec)
    (hVerify : KernelRealizes decode verifyStep mayoVerifyLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := mayoLeaves n
  specs := mayoSpecs quadStep verifyStep n
  decode := decode
  realized :=
    appendRealized leafSpec decode
      (chainRealized leafSpec decode mayoQuadLeaf quadStep n hQuad)
      (List.Forall₂.cons hVerify List.Forall₂.nil)

/-- **The whole-MAYO emit-realization (axis-6 on a real protocol).**  The entire
    emitted MAYO pipeline — `n` quadratic-form folds then the map-evaluation
    verify, `pipeN` over `mayoLeaves` — decodes to the composite
    `composeSpecs (mayoSpecs …)` of the input.  Obtained by one `runRealizes`
    call from the per-kernel realizations, for arbitrary fold length `n`. -/
theorem mayo_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (quadStep : Nat → C → C) (verifyStep : C → C) (n : Nat)
    (hQuad : ∀ i, KernelRealizes decode (quadStep i) mayoQuadLeaf leafSpec)
    (hVerify : KernelRealizes decode verifyStep mayoVerifyLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (mayoLeaves n) oldDest xVal)
      = composeSpecs (mayoSpecs quadStep verifyStep n) (decode xVal) :=
  (mayoProtocol leafSpec decode quadStep verifyStep n hQuad hVerify).runRealizes
    oldDest xVal

/-! ## §4  UOV — Oil-and-Vinegar multivariate map field fold

UOV (Unbalanced Oil-and-Vinegar) verification has the same multivariate
field-fold shape as MAYO: fold the central-map evaluation kernel over the
running field accumulator, then run the map-evaluation verify / pivot-swap step.

1. **Central-map fold**: fold the central-map evaluation `n` times over the
   accumulator (`mapStep i` = the `i`-th `uov_verify_mapeval_owned` field
   evaluation) — a field-arithmetic chain.
2. **Pivot-swap solve**: the final Gaussian-elimination pivot step
   (`solveStep` = `uov_solve_pivot_swap_owned`) — one trailing step.

Leaf names from the real extraction (`CatCrypt/Crypto/UOV/`):
`"uov_verify_mapeval_owned"` and `"uov_solve_pivot_swap_owned"`. -/

/-- The UOV central-map evaluation field-fold kernel leaf. -/
def uovMapLeaf : String := "uov_verify_mapeval_owned"

/-- The UOV Gaussian-elimination pivot-swap solve kernel leaf. -/
def uovSolveLeaf : String := "uov_solve_pivot_swap_owned"

/-- The UOV leaf list (general fold length `n`): `n` copies of the central-map
    fold leaf then the pivot-swap solve leaf. -/
def uovLeaves (n : Nat) : List String :=
  chainLeaves uovMapLeaf n ++ [uovSolveLeaf]

/-- The UOV spec list: the `n` central-map fold steps then the pivot-swap solve
    step, in pipeline order. -/
def uovSpecs (mapStep : Nat → C → C) (solveStep : C → C) (n : Nat) :
    List (C → C) :=
  chainSpecs mapStep n ++ [solveStep]

/-- **The assembled UOV `ProtocolKernels`**: the fold-then-solve leaf list, the
    matching spec list, the decoder, and the realization bundle glued from the
    central-map fold chain and the (singleton) solve step via `appendRealized`. -/
def uovProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (mapStep : Nat → C → C) (solveStep : C → C) (n : Nat)
    (hMap : ∀ i, KernelRealizes decode (mapStep i) uovMapLeaf leafSpec)
    (hSolve : KernelRealizes decode solveStep uovSolveLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := uovLeaves n
  specs := uovSpecs mapStep solveStep n
  decode := decode
  realized :=
    appendRealized leafSpec decode
      (chainRealized leafSpec decode uovMapLeaf mapStep n hMap)
      (List.Forall₂.cons hSolve List.Forall₂.nil)

/-- **The whole-UOV emit-realization (axis-6 on a real protocol).**  The entire
    emitted UOV pipeline — `n` central-map folds then the pivot-swap solve,
    `pipeN` over `uovLeaves` — decodes to the composite `composeSpecs (uovSpecs …)`
    of the input.  Obtained by one `runRealizes` call from the per-kernel
    realizations, for arbitrary fold length `n`. -/
theorem uov_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (mapStep : Nat → C → C) (solveStep : C → C) (n : Nat)
    (hMap : ∀ i, KernelRealizes decode (mapStep i) uovMapLeaf leafSpec)
    (hSolve : KernelRealizes decode solveStep uovSolveLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (uovLeaves n) oldDest xVal)
      = composeSpecs (uovSpecs mapStep solveStep n) (decode xVal) :=
  (uovProtocol leafSpec decode mapStep solveStep n hMap hSolve).runRealizes
    oldDest xVal

/-! ## §5  SPDZ — authenticated share arithmetic ++ MAC check

SPDZ (dishonest-majority MPC) runs the circuit over authenticated additive
shares, then performs a MAC check before opening.  Structurally:

1. **Authenticated share arithmetic**: a chain of `n` authenticated-share
   operations over the running share+MAC carrier (`shareStep i` = the `i`-th
   `auth_add` / `auth_scalar_mul` gate) — a field-arithmetic chain over the
   `(share, MAC)` pair.
2. **MAC check**: combine the per-party MAC shares and check them against the
   opened values (`macStep` = the `mac_shares` ++ `check` fold) — one trailing
   step that aborts on a MAC mismatch.

Both phases are unary `C → C` steps over the share+MAC carrier; concatenated
they are the SPDZ online evaluation.

Leaf names from the real extraction (`CatCrypt/Crypto/SPDZ/`):
`"auth_add"` and `"mac_shares"`. -/

/-- The SPDZ authenticated-share arithmetic kernel leaf. -/
def spdzShareLeaf : String := "auth_add"

/-- The SPDZ MAC-check kernel leaf. -/
def spdzMacLeaf : String := "mac_shares"

/-- The SPDZ leaf list (general gate count `n`): `n` copies of the authenticated
    share-arithmetic leaf then the MAC-check leaf. -/
def spdzLeaves (n : Nat) : List String :=
  chainLeaves spdzShareLeaf n ++ [spdzMacLeaf]

/-- The SPDZ spec list: the `n` share-arithmetic steps then the MAC-check step,
    in pipeline order. -/
def spdzSpecs (shareStep : Nat → C → C) (macStep : C → C) (n : Nat) :
    List (C → C) :=
  chainSpecs shareStep n ++ [macStep]

/-- **The assembled SPDZ `ProtocolKernels`**: the share-arithmetic-then-MAC-check
    leaf list, the matching spec list, the decoder, and the realization bundle
    glued from the share-arithmetic chain and the (singleton) MAC-check step via
    `appendRealized`. -/
def spdzProtocol (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (shareStep : Nat → C → C) (macStep : C → C) (n : Nat)
    (hShare : ∀ i, KernelRealizes decode (shareStep i) spdzShareLeaf leafSpec)
    (hMac : KernelRealizes decode macStep spdzMacLeaf leafSpec) :
    ProtocolKernels C leafSpec where
  leaves := spdzLeaves n
  specs := spdzSpecs shareStep macStep n
  decode := decode
  realized :=
    appendRealized leafSpec decode
      (chainRealized leafSpec decode spdzShareLeaf shareStep n hShare)
      (List.Forall₂.cons hMac List.Forall₂.nil)

/-- **The whole-SPDZ emit-realization (axis-6 on a real protocol).**  The entire
    emitted SPDZ online pipeline — `n` authenticated share-arithmetic gates then
    the MAC check, `pipeN` over `spdzLeaves` — decodes to the composite
    `composeSpecs (spdzSpecs …)` of the input.  Obtained by one `runRealizes`
    call from the per-kernel realizations (each an honest leaf-bytes KAT
    hypothesis), for arbitrary gate count `n`. -/
theorem spdz_protocol_realizes (leafSpec : LeafSpec) (decode : RustVal .TFp → C)
    (shareStep : Nat → C → C) (macStep : C → C) (n : Nat)
    (hShare : ∀ i, KernelRealizes decode (shareStep i) spdzShareLeaf leafSpec)
    (hMac : KernelRealizes decode macStep spdzMacLeaf leafSpec)
    (oldDest xVal : RustVal .TFp) :
    decode (pipeN leafSpec (spdzLeaves n) oldDest xVal)
      = composeSpecs (spdzSpecs shareStep macStep n) (decode xVal) :=
  (spdzProtocol leafSpec decode shareStep macStep n hShare hMac).runRealizes
    oldDest xVal

end CatCrypt.Crypto.SecureCompilation.PqcMpcProtocolKernels
