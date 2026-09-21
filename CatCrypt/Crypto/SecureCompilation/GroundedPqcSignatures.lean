/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.GroundedFieldProtocol
public import CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
public import CatCrypt.Crypto.SecureCompilation.GroundedMlkemNtt

/-!
# Grounded PQC SIGNATURE computational cores — whole-pipeline emit-realization
  with ZERO assumed per-kernel hypotheses

This module grounds the *computational cores* of three post-quantum
SIGNATURE families **unconditionally** — every per-step realization is a
*theorem* (a proved concrete realizer), so each strict headline carries **zero
`KernelRealizes` / `KernelRealizes2` / `KernelRealizesT` hypotheses** (only
codec-fit side conditions).  It reuses only the concrete
realizers already proved in-repo:

* `ConcreteSymFieldRealizer.fieldMul_realizes_concrete` /
  `fieldAdd_realizes_concrete` — the single-element base-256 `.TFp` field
  add/mul realizers, each decoding to `(· + ·)` / `(· * ·)` over `ZMod q` for
  **every** input (in turn the verified codec round-trip `decodeF_encodeF`).
  Strictly axiom-clean (`{propext, Classical.choice, Quot.sound}` only).
* `GroundedHashProtocol.keccakSponge_realized` + `pipeNT_realizes` — the
  carrier-`.TBytes 200` (1600-bit) Keccak sponge chain, every per-iteration
  realization the **proved** `ConcreteHashRealizer.keccak_realizes_concrete`
  (its 200-byte codec round-trip `decodeKbytes_encodeKbytes` proved per-bit,
  axiom-clean).
* `GroundedMlkemNtt.mlkem_ntt_computes_cyclicConv` — the proved leaf for the
  cyclic transform at (3329, 256, ω = 17), `nttMul 256 17 = cyclicConv 256`
  over `ZMod 3329`, on the `.TPolyMod 3329 256` carrier (used only in the
  isolated, non-portfolio §4 variant; it inherits the `native_decide` axioms
  for the root of unity 17 intrinsic to that carrier — see the Axioms note).
  That transform is multiplication modulo `X^256 − 1`, not FIPS 203's 7-layer
  transform modulo `X^256 + 1`.

## The grounded cores

* **`grounded_uov_central_map_realizes`** (MAYO / UOV multivariate, §1) — the
  central-map / oil–vinegar quadratic-form evaluation.  Each UOV/MAYO public-map
  component is `P(x) = Σ xᵢ xⱼ αᵢⱼ` — a multiply-accumulate over `Fq`.  We
  ground one multiply-accumulate step `acc ↦ acc + a · b` over the *binary*
  concrete field kernels (`fieldMul_realizes_concrete` then
  `fieldAdd_realizes_concrete`).  **ZERO kernel hypotheses** (only the codec
  fit).  Strictly axiom-clean.

* **`grounded_uov_seed_expand_realizes`** (MAYO / UOV SHAKE seed expansion, §2) —
  UOV/MAYO derive the bulk of the public key by expanding a short seed with
  SHAKE-128/256.  The `n`-block seed-expansion squeeze is the
  `pipeNT (.TBytes 200)` Keccak chain, every per-block realization the proved
  `keccak_realizes_concrete`.  **ZERO `KernelRealizesT` hypotheses.**  Strictly
  axiom-clean.

* **`grounded_vole_fiatshamir_realizes`** (Picnic / FAEST-style, §3) — the
  Fiat–Shamir / commitment hash chain of a hash-based / VOLE-in-the-head
  signature (Picnic's challenge hashes; FAEST's BAVC / VOLE-hash / commitment
  SHAKE absorbs).  The `n`-block transcript is the same `pipeNT (.TBytes 200)`
  Keccak chain, every per-block realization the proved `keccak_realizes_concrete`.
  **ZERO `KernelRealizesT` hypotheses.**  Strictly axiom-clean.

* **`grounded_lattice_sig_ntt_realizes`** (ISOLATED — §4, NOT in the strict
  portfolio) — the NTT-domain polynomial-multiply core shared by lattice
  SIGNATURE NTTs (ML-DSA / Dilithium NTT-multiply; the Falcon-style NTT
  convolution).  Modelled as a left fold of the proved leaf for the cyclic
  transform at (3329, 256, ω = 17), decoding to the iterated `cyclicConv 256`
  over `ZMod 3329`; neither ML-DSA's nor Falcon's transform is this object.  It
  carries the two `native_decide` axioms for the root of unity 17 intrinsic to
  the `.TPolyMod 3329 256` carrier (see Axioms note); it is therefore kept out
  of the strict portfolio, mirroring `GroundedFheThreshold`.

## Axioms

The strict portfolio (`grounded_pqc_signature_portfolio`) and §1–§3 are strictly
axiom-clean: `{propext, Classical.choice, Quot.sound}` only.

The §4 cyclic-transform variant `grounded_lattice_sig_ntt_realizes` inherits,
beyond the standard three, the two `native_decide` axioms for the root of
unity 17, `ConcreteNttRoots.pow_256_17_eq_one._native.native_decide.ax_1` and
`pow_128_17_ne_one._native.native_decide.ax_1` — because the carrier
`.TPolyMod 3329 256` requires the `Fact (Nat.Prime 3329)` instance and the
primitive-root fact `isPrimitiveRoot_17_256`, both established by `native_decide`
(the axioms of `GroundedMlkemNtt.grounded_mlkem_matvec_realizes`, the `k`-step
fold of `cyclicConv 256`, and of
`GroundedFheThreshold.grounded_fhe_ctmult_realizes`).  This is not a kernel
hypothesis; it is isolated out of the strict portfolio.

## Scope — what is grounded and what is not

* **Grounded (unconditional Lean theorem):** the *computational core* — that
  the emitted field-arithmetic / Keccak-sponge / NTT kernel pipeline computes its
  arithmetic spec.  Every per-step realization is a proved concrete realizer
  (`fieldMul`/`fieldAdd_realizes_concrete`, `keccak_realizes_concrete`,
  `mlkem_ntt_computes_cyclicConv`), no KAT, no per-kernel hypothesis.

* **The SIGNATURE SECURITY / hardness assumption is NOT grounded.**  We ground
  the computational core only — NOT EUF-CMA unforgeability, and NOT the
  underlying hardness (the MQ / oil–vinegar problem for UOV/MAYO, the
  picture-of-MPC / VOLE soundness for Picnic/FAEST, SIS / NTRU for the lattice
  signatures).  Those are separate, assumption-bearing results.  This file says
  only: *the emitted central-map / SHAKE-expand / Fiat–Shamir-hash / NTT kernel
  pipeline computes its arithmetic spec*, unconditionally.

* **Why SHAKE/Keccak and field-arithmetic and not bespoke primitives.**  Each
  core here has a proved concrete realizer whose codec round-trip is proved
  per-bit / by digit-sum (axiom-clean).  We ground only the primitives for which
  such a realizer already exists.  Falcon's own NTT prime (12289) has no
  proved realizer in-repo, so §4 uses the proved leaf for the cyclic transform
  at (3329, 256, ω = 17) as the carrier and is labeled as such (a cyclic
  convolution modulo `X^256 − 1`, not Falcon's modulus and not FIPS 203's
  transform).

* **The only machine-code residual (NOT a per-kernel hypothesis):** that the
  *jasmin-emitted machine bytes* of the real field-op / `keccak_f1600` /
  `ntt_poly_mul_3329_256` kernels equal the realizer leaf-specs — the
  owned-machine-code route, a single global obligation per kernel, explicitly not
  one of the per-step realizations this file discharges (nor a KAT).

## References
* NIST PQC: MAYO (Beullens et al.); UOV (Kipnis–Patarin–Goubin, CRYPTO 1999);
  Picnic (Chase et al., CCS 2017); FAEST (Baum et al., VOLE-in-the-head).
* FIPS 204 (ML-DSA / Dilithium); FIPS 205 (SLH-DSA); FIPS 202 (SHA-3 / SHAKE /
  Keccak sponge); Falcon (Fouque et al.).
* NIST FIPS 203 (ML-KEM, the NTT parameters `q = 3329`, `n = 256`, `ω = 17`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedPqcSignatures

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
open CatCrypt.Crypto.SecureCompilation.GroundedHashProtocol
open CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer
open CatCrypt.Crypto.SecureCompilation.GroundedMlkemNtt
open CatCrypt.Crypto.Optimizer.Lattice.CyclicConvolutionGeneric
open CatCrypt.Crypto.Hash.Keccak

/-! ## §1  MAYO / UOV central-map / oil–vinegar quadratic-form step — UNCONDITIONAL

A UOV / MAYO public map evaluates, per component, a quadratic form
`P(x) = Σᵢ Σⱼ αᵢⱼ xᵢ xⱼ` over `Fq`.  The inner kernel is a multiply-accumulate:
`acc ↦ acc + a · b` — one field multiply chained into one field add.  We express
the step over the *binary* concrete field kernels and prove its realization with
the two proved binary realizers — `fieldMul_realizes_concrete` then
`fieldAdd_realizes_concrete` — collapsing the encoded operand via the proved
round-trip `decodeF_encodeF`.  No `KernelRealizes2` hypothesis is assumed. -/

/-- The value of one UOV/MAYO multiply-accumulate step `(acc, a) ↦ acc + a · b`
    for a fixed coefficient operand `b`: apply the binary mul leaf to
    `(a, encodeF b)`, then the binary add leaf to `(acc, that product)`. -/
def uovMacStepValue (q : ℕ) [NeZero q] (width : ℕ) (b : ZMod q)
    (mulLeaf addLeaf : String) (limbStore : LimbStoreSpec)
    (oldDest accVal aVal : RustVal .TFp) : RustVal .TFp :=
  (fieldAddLeafSpec q width addLeaf limbStore).call addLeaf .TFp [.TFp, .TFp]
    oldDest
    [ ⟨.TFp, accVal⟩
    , ⟨.TFp,
        (fieldMulLeafSpec q width mulLeaf limbStore).call mulLeaf .TFp
          [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, encodeF width b⟩]⟩ ]

/-- **GROUNDED MAYO / UOV central-map multiply-accumulate step — UNCONDITIONAL.**

    The inner kernel of a UOV/MAYO oil–vinegar quadratic-form evaluation
    `P(x) = Σ αᵢⱼ xᵢ xⱼ` is the multiply-accumulate `acc ↦ acc + a · b` over `Fq`.
    Over the *binary* concrete field kernels it decodes to exactly
    `decodeF width accVal + decodeF width aVal * b` — with **ZERO
    `KernelRealizes2` hypotheses**.  Both per-kernel realizations are the proved
    `fieldMul_realizes_concrete` and `fieldAdd_realizes_concrete` (in turn the
    verified codec round-trip `decodeF_encodeF`); the encoded coefficient `b`
    collapses by `decodeF_encodeF`.  `width ≤ 48` and `q < 2^(8·width)` are the
    codec-fit side conditions, NOT kernel hypotheses.

    Scope:this grounds the *computational core* — the emitted
    multiply-accumulate kernel chain computes its field-arithmetic spec.  It does
    NOT prove UOV/MAYO EUF-CMA unforgeability nor the hardness of the MQ /
    oil–vinegar problem, which are separate assumption-bearing results.  The only
    residual is the owned-emit obligation for the two field-op leaves — NOT a
    per-kernel hypothesis. -/
theorem grounded_uov_central_map_realizes (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (b : ZMod q)
    (mulLeaf addLeaf : String) (limbStore : LimbStoreSpec)
    (oldDest accVal aVal : RustVal .TFp) :
    decodeF width
        (uovMacStepValue q width b mulLeaf addLeaf limbStore oldDest accVal aVal)
      = decodeF width accVal + decodeF width aVal * b := by
  unfold uovMacStepValue
  -- Outer add leaf realizes `(· + ·)` on its two decoded operands.
  rw [fieldAdd_realizes_concrete q width hw hq addLeaf limbStore accVal _ oldDest]
  -- Inner mul leaf realizes `(· * ·)` on its two decoded operands.
  rw [fieldMul_realizes_concrete q width hw hq mulLeaf limbStore aVal
        (encodeF width b) oldDest]
  -- Collapse the encoded coefficient via the proved round-trip.
  rw [decodeF_encodeF width hw hq]

/-! ## §2  MAYO / UOV SHAKE seed expansion — UNCONDITIONAL

UOV / MAYO derive the bulk of the public key from a short seed via SHAKE-128/256
expansion.  Each absorbed / squeezed SHAKE block is one application of the Keccak
permutation `keccak_f steps` to the 1600-bit sponge state.  The `n`-block
seed-expansion run is the `pipeNT (.TBytes 200)`-chain of `n` copies of
`"keccak_f1600"`, every per-block realization the proved
`keccak_realizes_concrete` — no hypothesis. -/

/-- The `n`-block UOV/MAYO seed-expansion leaf list: `n` copies of `"keccak_f1600"`
    (one Keccak permutation per absorbed/squeezed SHAKE block). -/
def uovSeedExpandLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-block spec list: `n` copies of `keccak_f steps`. -/
def uovSeedExpandSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED MAYO / UOV SHAKE seed-expansion core — UNCONDITIONAL.**

    UOV/MAYO expand a short seed into the bulk of the public key with
    SHAKE-128/256: `n` applications of the Keccak permutation `keccak_f steps` to
    the 1600-bit sponge state.  Its entire `pipeNT (.TBytes 200)` pipeline decodes
    to the composite of its per-block specs — with **ZERO `KernelRealizesT`
    hypotheses**.  Every per-block realization is the proved concrete realizer
    `keccak_realizes_concrete` (in turn the verified 200-byte codec round-trip
    `decodeKbytes_encodeKbytes`), assembled by `pipeNT_realizes`.

    Scope:this grounds the **SHAKE / Keccak-permutation seed-expansion
    core** of UOV/MAYO public-key generation.  The structural unpacking of the
    squeezed stream into the matrix/oil-space coefficients is NOT modeled, and
    UOV/MAYO EUF-CMA unforgeability / MQ hardness is out of scope.  The only
    residual is the owned-emit obligation for the `"keccak_f1600"` leaf — NOT a
    per-block hypothesis (and NOT a KAT). -/
theorem grounded_uov_seed_expand_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (uovSeedExpandLeaves n) oldDest xVal)
      = composeSpecs (uovSeedExpandSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (uovSeedExpandLeaves n) (uovSeedExpandSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §3  Picnic / FAEST-style VOLE / Fiat–Shamir commitment-hash — UNCONDITIONAL

A hash-based / VOLE-in-the-head signature (Picnic, FAEST) commits and derives its
Fiat–Shamir challenges via SHAKE / Keccak: Picnic's per-round challenge hashes;
FAEST's BAVC commitments, VOLE-hash, and challenge SHAKE absorbs.  Each block is
one application of `keccak_f steps` to the 1600-bit state.  The `n`-block
transcript is the `pipeNT (.TBytes 200)`-chain of `n` copies of `"keccak_f1600"`,
every per-block realization the proved `keccak_realizes_concrete` — no
hypothesis. -/

/-- The `n`-block Picnic/FAEST Fiat–Shamir / commitment-hash leaf list: `n` copies
    of `"keccak_f1600"` (one Keccak permutation per absorbed/squeezed block). -/
def voleFiatShamirLeaves (n : ℕ) : List String :=
  keccakSpongeLeaves n

/-- The matching per-block spec list: `n` copies of `keccak_f steps`. -/
def voleFiatShamirSpecs (steps : KeccakStepMappings) (n : ℕ) :
    List (KeccakState → KeccakState) :=
  keccakSpongeSpecs steps n

/-- **GROUNDED Picnic / FAEST-style Fiat–Shamir / commitment-hash — UNCONDITIONAL.**

    A hash-based / VOLE-in-the-head signature (Picnic; FAEST) derives its
    commitments and Fiat–Shamir challenges by SHAKE / Keccak hashing — `n`
    applications of the permutation `keccak_f steps` to the 1600-bit state.  Its
    entire `pipeNT (.TBytes 200)` pipeline decodes to the composite of its
    per-block specs — with **ZERO `KernelRealizesT` hypotheses**.  Every per-block
    realization is the proved concrete realizer `keccak_realizes_concrete` (in
    turn the verified 200-byte codec round-trip `decodeKbytes_encodeKbytes`),
    assembled by `pipeNT_realizes`.

    Scope:this grounds the **SHAKE / Keccak-permutation hash core** of
    the Picnic/FAEST commitment + Fiat–Shamir transcript.  The MPC-in-the-head /
    VOLE-in-the-head witness machinery (the GGM tree, the VOLE correlation, the
    ZK-hash bookkeeping) is NOT modeled, and Picnic/FAEST EUF-CMA / soundness is
    out of scope.  The only residual is the owned-emit obligation for the
    `"keccak_f1600"` leaf — NOT a per-block hypothesis (and NOT a KAT). -/
theorem grounded_vole_fiatshamir_realizes (steps : KeccakStepMappings)
    (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal (.TBytes 200)) :
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (voleFiatShamirLeaves n) oldDest xVal)
      = composeSpecs (voleFiatShamirSpecs steps n) (decodeKbytes xVal) :=
  pipeNT_realizes (.TBytes 200) decodeKbytes
    (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
      "keccak_f1600" limbStore)
    (voleFiatShamirLeaves n) (voleFiatShamirSpecs steps n)
    (keccakSponge_realized steps limbStore n) oldDest xVal

/-! ## §4  Lattice-signature polynomial-multiply core over the cyclic
  transform — isolated from the strict portfolio

ML-DSA / Dilithium (and Falcon-style) signatures do their core polynomial
arithmetic in an evaluation domain: each polynomial product is a pointwise
multiply there.  We model the iterated multiply core as a left fold of the
leaf `mlkemNttLeafSpec`, which realizes the cyclic transform at
(3329, 256, ω = 17) — `nttMul 256 17 = cyclicConv 256` over `ZMod 3329`,
multiplication modulo `X^256 − 1` — every per-step realization the proved
`mlkem_ntt_computes_cyclicConv`, decoding to the iterated `cyclicConv 256`.
Neither ML-DSA's transform (modulo `X^256 + 1` at `q = 8380417`) nor Falcon's
(prime 12289) is this object, and it is not FIPS 203's 7-layer transform either.

Falcon's own prime (12289) has no proved realizer here, so this grounds the
polynomial-multiply core over the proved (3329, 256, ω = 17) carrier and is
labeled as such.  Because the `.TPolyMod 3329 256` carrier needs the
`Fact (Nat.Prime 3329)` instance and the primitive root `isPrimitiveRoot_17_256`
(both `native_decide`), this theorem carries the two `native_decide` axioms for
the root of unity 17 (see the module Axioms note) and is therefore kept out of
the strict portfolio (§5). -/

/-- The value of a `k`-factor lattice-signature polynomial-multiply chain: fold
    the operand polynomials `ps` left-to-right, each step multiplying the running
    accumulator against the next factor via the proved `mlkemNttLeafSpec` leaf
    (the cyclic transform at (3329, 256, ω = 17)). -/
def latticeSigNttChainValue (limbStore : LimbStoreSpec)
    (oldDest : RustVal (.TPolyMod 3329 256))
    (ps : List (RustVal (.TPolyMod 3329 256)))
    (acc0 : RustVal (.TPolyMod 3329 256)) : RustVal (.TPolyMod 3329 256) :=
  ps.foldl
    (fun acc p =>
      (mlkemNttLeafSpec limbStore).call "ntt_poly_mul_3329_256"
        (.TPolyMod 3329 256) [.TPolyMod 3329 256, .TPolyMod 3329 256] oldDest
        [⟨.TPolyMod 3329 256, acc⟩, ⟨.TPolyMod 3329 256, p⟩])
    acc0

/-- The matching abstract spec: fold `cyclicConv 256` against the decoded operand
    polynomials, left-to-right. -/
def latticeSigNttChainSpec (ps : List (RustVal (.TPolyMod 3329 256)))
    (acc0 : Fin 256 → ZMod 3329) : Fin 256 → ZMod 3329 :=
  ps.foldl (fun acc p => cyclicConv 256 acc (mlkemDecode p)) acc0

/-- The lattice-signature polynomial-multiply chain over the cyclic transform at
    (3329, 256, ω = 17), realized with no kernel hypothesis; isolated from the
    strict portfolio.

    ML-DSA / Dilithium (and Falcon-style) signatures multiply polynomials in an
    evaluation domain.  The whole `k`-factor chain here decodes to the iterated
    cyclic convolution of the decoded operands, with no kernel hypothesis.
    Every per-factor step is the proved `mlkem_ntt_computes_cyclicConv`, the
    realization of `nttMul 256 17 = cyclicConv 256` over `ZMod 3329` (the
    verified `.TPolyMod 3329 256` codec round-trip `decodeP_encodeP` + the
    primitive root `isPrimitiveRoot_17_256`).  That transform is multiplication
    modulo `X^256 − 1`; it is not FIPS 203's transform, not ML-DSA's and not
    Falcon's.

    Scope: this grounds the computational core — the emitted
    cyclic-convolution chain computes its polynomial-arithmetic spec.  It does
    not prove ML-DSA / Falcon EUF-CMA unforgeability nor the SIS / NTRU
    hardness.  Falcon's own prime (12289) has no proved realizer, so this uses
    the proved (3329, 256, ω = 17) leaf as the carrier.  The only residual is
    the owned-emit obligation for the `"ntt_poly_mul_3329_256"` leaf — not a
    per-step hypothesis.

    Axioms: this theorem inherits, beyond the standard three
    `{propext, Classical.choice, Quot.sound}`, the two `native_decide` axioms
    for the root of unity 17 (`pow_256_17_eq_one`, `pow_128_17_ne_one`) carried
    by the `.TPolyMod 3329 256` carrier — the axioms of
    `GroundedMlkemNtt.grounded_mlkem_matvec_realizes` (the `k`-step fold of
    `cyclicConv 256`) and `GroundedFheThreshold.grounded_fhe_ctmult_realizes`.
    It is not a kernel hypothesis; the strict portfolio (§5) is grounded through
    the strictly axiom-clean field + Keccak cores instead. -/
theorem grounded_lattice_sig_ntt_realizes (limbStore : LimbStoreSpec)
    (oldDest : RustVal (.TPolyMod 3329 256))
    (ps : List (RustVal (.TPolyMod 3329 256)))
    (acc0 : RustVal (.TPolyMod 3329 256)) :
    mlkemDecode (latticeSigNttChainValue limbStore oldDest ps acc0)
      = latticeSigNttChainSpec ps (mlkemDecode acc0) := by
  unfold latticeSigNttChainValue latticeSigNttChainSpec
  induction ps generalizing acc0 with
  | nil => simp
  | cons p restP ih =>
      simp only [List.foldl_cons]
      rw [ih ((mlkemNttLeafSpec limbStore).call "ntt_poly_mul_3329_256"
        (.TPolyMod 3329 256) [.TPolyMod 3329 256, .TPolyMod 3329 256] oldDest
        [⟨.TPolyMod 3329 256, acc0⟩, ⟨.TPolyMod 3329 256, p⟩])]
      rw [mlkem_ntt_computes_cyclicConv limbStore acc0 p oldDest]

/-! ## §5  The strict PQC-SIGNATURE headline — three strictly-clean cores

The strict PQC-signature portfolio conjoins the three strictly axiom-clean
cores: the MAYO/UOV central-map multiply-accumulate field step, the MAYO/UOV
SHAKE seed-expansion Keccak chain, and the Picnic/FAEST Fiat–Shamir Keccak chain.
All three are unconditional in their kernels and strictly axiom-clean
(`{propext, Classical.choice, Quot.sound}`).  The §4 cyclic-transform core
is kept out of the strict portfolio: it carries the two `native_decide` axioms
for the root of unity 17 intrinsic to the `.TPolyMod 3329 256` carrier (see the
§4 axiom paragraph), mirroring `GroundedFheThreshold`.  Each conjunct grounds a *computational
core*, not a signature-security property. -/

/-- **THE PQC-SIGNATURE HEADLINE — three strictly axiom-clean cores, ZERO
    kernel hypotheses.**

    The three PQC-signature cores conjoined:

    * the MAYO / UOV central-map oil–vinegar multiply-accumulate field step,
    * the MAYO / UOV SHAKE seed-expansion Keccak sponge, and
    * the Picnic / FAEST-style Fiat–Shamir / commitment Keccak sponge,

    each with **ZERO kernel hypotheses** — every per-step realization is a proved
    concrete realizer (`fieldMul`/`fieldAdd_realizes_concrete` for the field step,
    `keccak_realizes_concrete` for the two hash chains), in turn a verified codec
    round-trip.  All three are strictly axiom-clean
    (`{propext, Classical.choice, Quot.sound}`).

    The §4 lattice-signature core (`grounded_lattice_sig_ntt_realizes`)
    grounds the iterated `cyclicConv 256` over `ZMod 3329` but inherits the two
    `native_decide` axioms for the root of unity 17 intrinsic to the
    `.TPolyMod 3329 256` carrier (see the §4 axiom paragraph and the module
    Axioms section); it is therefore kept out of this strict portfolio,
    mirroring `GroundedFheThreshold`.

    Scope:each conjunct grounds the *computational core* — that the
    emitted central-map / SHAKE-expand / Fiat–Shamir-hash kernel pipeline computes
    its arithmetic spec.  It does NOT prove the PQC-signature security (UOV/MAYO,
    Picnic/FAEST EUF-CMA unforgeability) nor the underlying hardness (MQ /
    oil–vinegar, MPC/VOLE soundness), which are separate assumption-bearing
    results.  The only residuals are the per-kernel machine-code obligations
    (owned-emit route). -/
theorem grounded_pqc_signature_portfolio (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width)) (b : ZMod q)
    (mulLeaf addLeaf : String) (limbStore : LimbStoreSpec)
    (uovOldDest uovAccVal uovAVal : RustVal .TFp)
    (steps : KeccakStepMappings) (n : ℕ)
    (seedOldDest seedXVal voleOldDest voleXVal : RustVal (.TBytes 200)) :
    -- MAYO/UOV central-map multiply-accumulate field step: grounded, only codec fit.
    decodeF width
        (uovMacStepValue q width b mulLeaf addLeaf limbStore
          uovOldDest uovAccVal uovAVal)
      = decodeF width uovAccVal + decodeF width uovAVal * b
    ∧
    -- MAYO/UOV SHAKE seed-expansion Keccak sponge: grounded, no kernel hypotheses.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (uovSeedExpandLeaves n) seedOldDest seedXVal)
      = composeSpecs (uovSeedExpandSpecs steps n) (decodeKbytes seedXVal)
    ∧
    -- Picnic/FAEST Fiat–Shamir / commitment Keccak sponge: grounded, no kernel hypotheses.
    decodeKbytes
        (pipeNT (.TBytes 200)
          (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
            "keccak_f1600" limbStore)
          (voleFiatShamirLeaves n) voleOldDest voleXVal)
      = composeSpecs (voleFiatShamirSpecs steps n) (decodeKbytes voleXVal) :=
  ⟨grounded_uov_central_map_realizes q width hw hq b mulLeaf addLeaf limbStore
     uovOldDest uovAccVal uovAVal,
   grounded_uov_seed_expand_realizes steps limbStore n seedOldDest seedXVal,
   grounded_vole_fiatshamir_realizes steps limbStore n voleOldDest voleXVal⟩

end CatCrypt.Crypto.SecureCompilation.GroundedPqcSignatures
