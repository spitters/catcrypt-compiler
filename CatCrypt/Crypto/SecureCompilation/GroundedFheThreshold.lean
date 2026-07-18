/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.GroundedMlkemNtt
import CatCrypt.Crypto.SecureCompilation.ConcreteBarrettRealizer
import CatCrypt.Crypto.SecureCompilation.ConcreteMontMulRealizer

/-!
# Grounded FHE / threshold lattice-arithmetic backbones — whole-pipeline
  emit-realization with ZERO assumed per-kernel hypotheses

The computational core of BGV / BFV / CKKS homomorphic evaluation and of
lattice-based threshold decryption / distributed key generation is the SAME
arithmetic the ML-KEM / ML-DSA portfolio already grounds: **NTT-domain
polynomial multiplication** (`nttMul = cyclicConv` at a proven primitive root)
and **coefficient modular reduction** (Barrett `barrettCondsub`).  This module
grounds three of these backbones **unconditionally** — every per-step
realization is a *theorem* (a proved concrete realizer), so each headline carries
**zero `NttEmitRealizesP` / `KernelRealizes` hypotheses** (only codec-fit / range
side conditions, honestly flagged).  It reuses the proved concrete realizers
already in-repo:

* `GroundedMlkemNtt.mlkem_ntt_computes_cyclicConv` — the ML-KEM NTT-multiply
  leaf over the `.TPolyMod 3329 256` carrier, decoding to `cyclicConv 256` for
  **every** input (in turn `ConcreteNttRealizer.mlkem_nttEmitRealizes_concrete`
  + the verified `.TPolyMod` codec round-trip `decodeP_encodeP` + the proven
  primitive root `isPrimitiveRoot_17_256`).  Axiom-clean
  (`{propext, Classical.choice, Quot.sound}` only).
* `ConcreteBarrettRealizer.barrett_realizes_concrete` — the Barrett
  modular-reduction leaf over the base-256 `.TFp` codec, decoding to
  `barrettCondsub q k` for **every** input (in turn the verified round-trip
  `decodeB_encodeB`).  The `barrettCondsub` form is fully unconditional and
  strictly axiom-clean.
* `ConcreteMontMulRealizer.montMul_realizes_concrete` — the Montgomery-domain
  coefficient-multiply leaf over the base-256 `.TFp` codec, decoding to
  `montMul N R N'` for **every** input (in turn the verified round-trip
  `decodeZ_encodeZ`).  Strictly axiom-clean.
* `ProtocolEmitRealizes.pipeN` / `composeSpecs` — the carrier-`.TFp` unary
  composition law for the reduction chain.

## Axioms (honest flag)

The two NTT backbones (`grounded_fhe_ctmult_realizes`,
`grounded_threshold_combine_realizes`) inherit, beyond the standard three
`{propext, Classical.choice, Quot.sound}`, the two axioms
`ConcreteNttRoots.pow_256_17_eq_one._native.native_decide.ax_1` and
`pow_128_17_ne_one._native.native_decide.ax_1` — because the ML-KEM polynomial
carrier `.TPolyMod 3329 256` requires the `Fact (Nat.Prime 3329)` instance and
the primitive-root fact `isPrimitiveRoot_17_256`, both established by
`native_decide`.  This is EXACTLY the axiom set already carried by the in-repo
reference `GroundedMlkemNtt.grounded_mlkem_matvec_realizes` over the same proved
realizer; it is NOT a kernel hypothesis.  Mirroring
`GroundedMpcZk` (whose permutation-path theorems carry the analogous BabyBear
`native_decide` axiom while its strict PORTFOLIO is grounded through a strictly
axiom-clean conjunct), the two strictly axiom-clean `.TFp` backbones — the
Barrett modulus-switch reduce chain and the Montgomery-domain coefficient
multiply — are the ones conjoined in the strict portfolio
`grounded_fhe_threshold_portfolio` (`{propext, Classical.choice, Quot.sound}`
only); the `native_decide`-carrying NTT chains are kept out of it.

## The four grounded backbones

* **`grounded_fhe_ctmult_realizes`** — the FHE ciphertext-multiply / key-switch
  NTT pipeline.  A BGV/BFV/CKKS homomorphic multiply (and the relinearization /
  key-switch that follows) is, in the NTT domain, repeated pointwise
  NTT-multiply of the operand polynomials: `c ↦ c ⊛ kᵢ` for the key-switching /
  ciphertext factors `kᵢ`.  We model the `k`-factor chain as a left fold of the
  grounded `mlkemNttLeafSpec` NTT-multiply leaf, every per-step realization the
  proved `mlkem_ntt_computes_cyclicConv` — so the whole chain decodes to the
  iterated `cyclicConv 256`.  **ZERO kernel hypotheses.**

* **`grounded_threshold_combine_realizes`** — the threshold-decryption /
  distributed-KeyGen NTT-domain share-combine.  In a lattice threshold scheme,
  each party publishes an NTT-domain partial decryption (or key share) and the
  combiner accumulates them.  We ground the NTT-domain combine backbone as a
  left fold of the same grounded NTT-multiply leaf over the share list — the
  accumulate-of-NTT-domain-shares pattern — decoding to the iterated
  `cyclicConv 256` of the decoded shares.  **ZERO kernel hypotheses.**

* **`grounded_bfv_modswitch_realizes`** — the BFV/BGV modulus-switch / rescale
  step.  Rescaling drops a coefficient from modulus `Q` to `Q'` by a rounded
  divide-and-reduce; its modular-reduction backbone is a Barrett `condsub`
  applied per coefficient, iterated over the `n` coefficients of the polynomial.
  We model the `n`-coefficient reduce chain as a `pipeN` of the grounded Barrett
  leaf, every per-step realization the proved `barrett_realizes_concrete` — so
  the whole chain decodes to the iterated `barrettCondsub q k`.  **ZERO kernel
  hypotheses.**

* **`grounded_fhe_montmul_coeff_realizes`** — the Montgomery-domain
  coefficient-multiply primitive used throughout RNS BFV/CKKS coefficient
  arithmetic (and ML-DSA / ML-KEM Montgomery multiply).  A single coefficient
  product in the Montgomery domain is `montMul N R N'`; the grounded Montgomery
  leaf `montMulLeafSpec` realizes it as a `KernelRealizes2` theorem for every
  input (the proved `montMul_realizes_concrete`).  **ZERO kernel hypotheses**
  (only the codec-fit residue-range side condition).

## HONEST scope — what is grounded and what is NOT

* **Grounded (unconditional Lean theorem):** every per-step realization of all
  three backbones — each a proved concrete realizer
  (`mlkem_ntt_computes_cyclicConv`, `barrett_realizes_concrete`), with no KAT and
  no per-kernel hypothesis.  Each whole pipeline decodes to the composite of its
  per-step arithmetic specs.

* **The FHE / THRESHOLD SECURITY property is NOT what is grounded here.**  We
  ground the *computational backbone* — the emitted NTT / reduce KERNEL PIPELINE
  computes its arithmetic spec — NOT the cryptographic properties of the
  construction.  Concretely: FHE SEMANTIC SECURITY (IND-CPA under RLWE), the
  NOISE-GROWTH / correctness bounds of homomorphic multiply and of modulus
  switching, threshold-decryption PRIVACY (a corrupt minority learns nothing) and
  ROBUSTNESS, and distributed-KeyGen SIMULATABILITY are separate,
  assumption-bearing results proved elsewhere (or out of scope).  This file says
  only: *the emitted NTT-multiply / Barrett-reduce kernel pipeline computes its
  polynomial-arithmetic spec*, unconditionally.

* **Why NTT-multiply / Barrett and not a bespoke FHE primitive.**  Each backbone
  here has a proved concrete realizer whose codec round-trip is proved per-bit /
  by digit-sum (axiom-clean).  We ground only the arithmetic primitives for which
  such a realizer already exists (`nttMul`, `barrettCondsub`); FHE-specific
  operations with no proved realizer (e.g. RNS base conversion, automorphism /
  Galois key application as bespoke kernels) are deliberately NOT grounded here.

* **The only machine-code residual (NOT a per-kernel hypothesis):** that the
  *jasmin-emitted machine bytes* of the real `ntt_poly_mul_3329_256` /
  Barrett-reduce kernels equal the realizer leaf-specs — the owned-machine-code
  route, a single global obligation per kernel, explicitly not one of the
  per-step realizations this file discharges (nor a KAT).

## References
* Brakerski–Gentry–Vaikuntanathan, *(Leveled) FHE without bootstrapping* (BGV),
  ITCS 2012; Fan–Vercauteren, *Somewhat practical FHE* (BFV), ePrint 2012/144;
  Cheon–Kim–Kim–Song, *HE for arithmetic of approximate numbers* (CKKS),
  ASIACRYPT 2017.
* Boneh et al., *Threshold cryptosystems from threshold FHE*, CRYPTO 2018;
  Asharov et al., *Multiparty computation with low communication … threshold
  FHE*, EUROCRYPT 2012.
* P. Barrett, CRYPTO 1986 (Barrett reduction).  NIST FIPS 203 (ML-KEM, the NTT
  parameters `q = 3329`, `n = 256`, `ω = 17`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GroundedFheThreshold

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GroundedMlkemNtt
open CatCrypt.Crypto.SecureCompilation.ConcreteBarrettRealizer
open CatCrypt.Crypto.SecureCompilation.ConcreteMontMulRealizer
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.Optimizer.Lattice.CyclicConvolutionGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric

/-! ## §1  FHE ciphertext-multiply / key-switch NTT pipeline — UNCONDITIONAL

A BGV/BFV/CKKS homomorphic multiply followed by relinearization / key-switching
is, in the NTT (evaluation) domain, a sequence of pointwise polynomial
multiplications of the operand against the ciphertext / key-switching factors:
`c ↦ c ⊛ k₁ ⊛ k₂ ⊛ ⋯`.  Each `⊛` is one NTT-domain pointwise multiply, which the
grounded ML-KEM NTT-multiply leaf `mlkemNttLeafSpec` realizes as `cyclicConv 256`
for every input (the proved `mlkem_ntt_computes_cyclicConv`).  The `k`-factor
chain is therefore a left fold of that grounded leaf, decoding to the iterated
`cyclicConv 256` — with **ZERO kernel hypotheses**.

We work at the value level over the `.TPolyMod 3329 256` carrier (as
`GroundedMlkemNtt.matvecChainValue` does), since the NTT-multiply is *binary*. -/

/-- The value of a `k`-factor FHE ciphertext-multiply / key-switch chain: fold the
    key-switching / ciphertext factors `ks` left-to-right, each step multiplying
    the running ciphertext accumulator against the next factor via the grounded
    `mlkemNttLeafSpec` NTT-multiply leaf. -/
def fheCtMultChainValue (limbStore : LimbStoreSpec)
    (oldDest : RustVal (.TPolyMod 3329 256))
    (ks : List (RustVal (.TPolyMod 3329 256)))
    (ct0 : RustVal (.TPolyMod 3329 256)) : RustVal (.TPolyMod 3329 256) :=
  ks.foldl
    (fun acc k =>
      (mlkemNttLeafSpec limbStore).call "ntt_poly_mul_3329_256"
        (.TPolyMod 3329 256) [.TPolyMod 3329 256, .TPolyMod 3329 256] oldDest
        [⟨.TPolyMod 3329 256, acc⟩, ⟨.TPolyMod 3329 256, k⟩])
    ct0

/-- The matching abstract spec of the `k`-factor FHE ciphertext-multiply chain:
    fold `cyclicConv 256` against the decoded key-switching / ciphertext factors,
    left-to-right — the iterated NTT-domain pointwise product. -/
def fheCtMultChainSpec (ks : List (RustVal (.TPolyMod 3329 256)))
    (ct0 : Fin 256 → ZMod 3329) : Fin 256 → ZMod 3329 :=
  ks.foldl (fun acc k => cyclicConv 256 acc (mlkemDecode k)) ct0

/-- **GROUNDED FHE ciphertext-multiply / key-switch NTT pipeline — UNCONDITIONAL.**

    A BGV/BFV/CKKS homomorphic multiply + relinearization / key-switch is, in the
    NTT domain, repeated pointwise polynomial multiply of the ciphertext against
    the `k` key-switching / ciphertext factors.  Its whole `k`-factor chain
    decodes to the iterated cyclic convolution of the decoded operands — with
    **ZERO kernel hypotheses**.  Every per-factor step is the proved
    `mlkem_ntt_computes_cyclicConv` (itself the unconditional grounded ML-KEM
    NTT-multiply realization: the verified `.TPolyMod 3329 256` codec round-trip
    `decodeP_encodeP` + the proven primitive root `isPrimitiveRoot_17_256`).

    HONEST scope: this grounds the *computational backbone* — the emitted NTT
    pointwise-multiply chain computes its polynomial-arithmetic spec.  It does NOT
    prove the FHE scheme's SEMANTIC SECURITY (IND-CPA under RLWE) nor the
    NOISE-GROWTH / correctness bound of homomorphic multiply, which are separate
    results.  The only residual is the machine-code obligation for the
    `"ntt_poly_mul_3329_256"` leaf — the owned-machine-code route, NOT a per-step
    hypothesis.

    AXIOM NOTE (honest flag): this theorem inherits, beyond the standard three
    `{propext, Classical.choice, Quot.sound}`, the two ML-KEM-root `native_decide`
    axioms (`pow_256_17_eq_one`, `pow_128_17_ne_one`) carried by the ML-KEM NTT
    carrier `.TPolyMod 3329 256` — exactly the axioms of the in-repo reference
    `GroundedMlkemNtt.grounded_mlkem_matvec_realizes`.  It is NOT a kernel
    hypothesis; the strict portfolio (§5) is grounded through the two strictly
    axiom-clean `.TFp` backbones instead. -/
theorem grounded_fhe_ctmult_realizes (limbStore : LimbStoreSpec)
    (oldDest : RustVal (.TPolyMod 3329 256))
    (ks : List (RustVal (.TPolyMod 3329 256)))
    (ct0 : RustVal (.TPolyMod 3329 256)) :
    mlkemDecode (fheCtMultChainValue limbStore oldDest ks ct0)
      = fheCtMultChainSpec ks (mlkemDecode ct0) := by
  unfold fheCtMultChainValue fheCtMultChainSpec
  induction ks generalizing ct0 with
  | nil => simp
  | cons k restK ih =>
      simp only [List.foldl_cons]
      rw [ih ((mlkemNttLeafSpec limbStore).call "ntt_poly_mul_3329_256"
        (.TPolyMod 3329 256) [.TPolyMod 3329 256, .TPolyMod 3329 256] oldDest
        [⟨.TPolyMod 3329 256, ct0⟩, ⟨.TPolyMod 3329 256, k⟩])]
      rw [mlkem_ntt_computes_cyclicConv limbStore ct0 k oldDest]

/-! ## §2  Threshold-decryption / distributed-KeyGen NTT-domain share-combine —
  UNCONDITIONAL

In a lattice-based threshold cryptosystem (threshold FHE, distributed key
generation), each party publishes an NTT-domain partial decryption / key share
and the combiner accumulates them in the evaluation domain.  The combine backbone
is the same NTT-domain pointwise operation iterated over the share list.  We
ground the NTT-domain share-combine as a left fold of the grounded
`mlkemNttLeafSpec` NTT-multiply leaf — the accumulate-of-NTT-domain-shares
pattern — decoding to the iterated `cyclicConv 256` of the decoded shares, with
**ZERO kernel hypotheses**.  (The fold shape is shared with §1; here it is the
share-combine of a threshold protocol rather than a ciphertext-multiply chain.)
-/

/-- The value of a threshold NTT-domain share-combine: fold the parties' NTT-domain
    shares `shares` left-to-right, each step combining the running accumulator
    against the next share via the grounded `mlkemNttLeafSpec` NTT-domain leaf. -/
def thresholdCombineValue (limbStore : LimbStoreSpec)
    (oldDest : RustVal (.TPolyMod 3329 256))
    (shares : List (RustVal (.TPolyMod 3329 256)))
    (acc0 : RustVal (.TPolyMod 3329 256)) : RustVal (.TPolyMod 3329 256) :=
  shares.foldl
    (fun acc s =>
      (mlkemNttLeafSpec limbStore).call "ntt_poly_mul_3329_256"
        (.TPolyMod 3329 256) [.TPolyMod 3329 256, .TPolyMod 3329 256] oldDest
        [⟨.TPolyMod 3329 256, acc⟩, ⟨.TPolyMod 3329 256, s⟩])
    acc0

/-- The matching abstract spec of the threshold share-combine: fold `cyclicConv
    256` against the decoded NTT-domain shares, left-to-right. -/
def thresholdCombineSpec (shares : List (RustVal (.TPolyMod 3329 256)))
    (acc0 : Fin 256 → ZMod 3329) : Fin 256 → ZMod 3329 :=
  shares.foldl (fun acc s => cyclicConv 256 acc (mlkemDecode s)) acc0

/-- **GROUNDED threshold-decryption / distributed-KeyGen NTT-domain share-combine
    — UNCONDITIONAL.**

    A lattice threshold scheme combines parties' NTT-domain partial decryptions /
    key shares in the evaluation domain.  Its whole `pipeN`-style share-combine
    chain decodes to the iterated cyclic convolution of the decoded shares — with
    **ZERO kernel hypotheses**.  Every per-share step is the proved
    `mlkem_ntt_computes_cyclicConv` (the unconditional grounded NTT-domain leaf).

    HONEST scope: this grounds the *computational backbone* — the emitted
    NTT-domain combine chain computes its polynomial-arithmetic spec.  It does NOT
    prove the threshold scheme's PRIVACY (a corrupt minority learns nothing about
    the secret key / plaintext), ROBUSTNESS, nor distributed-KeyGen
    SIMULATABILITY, which are separate cryptographic results.  The only residual
    is the machine-code obligation for the `"ntt_poly_mul_3329_256"` leaf — the
    owned-machine-code route, NOT a per-step hypothesis.

    AXIOM NOTE (honest flag): as for §1, this NTT-route theorem inherits the two
    ML-KEM-root `native_decide` axioms carried by the `.TPolyMod 3329 256` carrier
    (the same as the in-repo reference `grounded_mlkem_matvec_realizes`); it is NOT
    a kernel hypothesis, and the strict portfolio (§5) is grounded through the two
    strictly axiom-clean `.TFp` backbones instead. -/
theorem grounded_threshold_combine_realizes (limbStore : LimbStoreSpec)
    (oldDest : RustVal (.TPolyMod 3329 256))
    (shares : List (RustVal (.TPolyMod 3329 256)))
    (acc0 : RustVal (.TPolyMod 3329 256)) :
    mlkemDecode (thresholdCombineValue limbStore oldDest shares acc0)
      = thresholdCombineSpec shares (mlkemDecode acc0) := by
  unfold thresholdCombineValue thresholdCombineSpec
  induction shares generalizing acc0 with
  | nil => simp
  | cons s restS ih =>
      simp only [List.foldl_cons]
      rw [ih ((mlkemNttLeafSpec limbStore).call "ntt_poly_mul_3329_256"
        (.TPolyMod 3329 256) [.TPolyMod 3329 256, .TPolyMod 3329 256] oldDest
        [⟨.TPolyMod 3329 256, acc0⟩, ⟨.TPolyMod 3329 256, s⟩])]
      rw [mlkem_ntt_computes_cyclicConv limbStore acc0 s oldDest]

/-! ## §3  BFV/BGV modulus-switch / rescale Barrett reduce chain — UNCONDITIONAL

A BFV/BGV modulus switch (or a CKKS rescale) drops each coefficient from a larger
modulus to a smaller one by a rounded divide and a modular reduction; its
modular-reduction backbone is a Barrett conditional-subtract `barrettCondsub q k`
applied per coefficient.  Iterating it over the `n` coefficients of the
polynomial is a `pipeN` of the grounded Barrett leaf, every per-coefficient step
the proved `barrett_realizes_concrete` — so the whole reduce chain decodes to the
iterated `barrettCondsub q k`, with **ZERO kernel hypotheses**.

We use the unary `.TFp`-carrier `pipeN` composition law: each coefficient is a
`.TFp` natural-number slot, and `barrettLeafSpec` is the proved unary reduce
leaf. -/

/-- The `n`-coefficient modulus-switch reduce leaf list: `n` copies of the Barrett
    reduce leaf `leaf` (one conditional-subtract per coefficient). -/
def modSwitchLeaves (leaf : String) (n : ℕ) : List String :=
  List.replicate n leaf

/-- The matching per-coefficient spec list: `n` copies of `barrettCondsub q k`. -/
def modSwitchSpecs (q k n : ℕ) : List (ℕ → ℕ) :=
  List.replicate n (fun x => barrettCondsub q k x)

/-- The position-wise `Forall₂` of per-coefficient realizations for the
    modulus-switch reduce chain — `n` copies of the **proved**
    `barrett_realizes_concrete`.  No hypothesis is assumed; every entry is
    discharged unconditionally (only the codec-fit `width ≤ 48`). -/
theorem modSwitch_realized (q k width : ℕ) (hw : width ≤ 48)
    (leaf : String) (limbStore : LimbStoreSpec) (n : ℕ) :
    List.Forall₂
      (fun l s => KernelRealizes (decodeB width) s l
        (barrettLeafSpec q k width leaf limbStore))
      (modSwitchLeaves leaf n) (modSwitchSpecs q k n) := by
  unfold modSwitchLeaves modSwitchSpecs
  induction n with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact List.Forall₂.cons
        (barrett_realizes_concrete q k width hw leaf limbStore) ih

/-- **GROUNDED BFV/BGV modulus-switch / rescale reduce chain — UNCONDITIONAL.**

    A BFV/BGV modulus switch (or CKKS rescale) reduces each of the `n`
    polynomial coefficients by a Barrett conditional-subtract.  Its entire
    `pipeN` (`.TFp` carrier) reduce pipeline decodes to the composite of its
    per-coefficient specs — `n` copies of `barrettCondsub q k` — with **ZERO
    `KernelRealizes` hypotheses**.  Every per-coefficient realization is the
    proved concrete realizer `barrett_realizes_concrete` (in turn the verified
    base-256 codec round-trip `decodeB_encodeB`), assembled by `pipeN_realizes`.

    `width ≤ 48` is the codec-fit side condition (the `width` base-256 digits fit
    the 48-byte carrier); it is NOT a kernel hypothesis — the Barrett realizer is
    unconditional.

    HONEST scope: this grounds the *computational backbone* — the emitted Barrett
    reduce chain computes its modular-reduction spec.  It does NOT prove the
    correctness of the modulus-switch ROUNDING (that the rescaled ciphertext
    decrypts to the scaled plaintext within the noise budget), which is a separate
    noise-analysis result.  The only residual is the machine-code obligation for
    the Barrett reduce leaf — the owned-machine-code route, NOT a per-coefficient
    hypothesis. -/
theorem grounded_bfv_modswitch_realizes (q k width : ℕ) (hw : width ≤ 48)
    (leaf : String) (limbStore : LimbStoreSpec) (n : ℕ)
    (oldDest xVal : RustVal .TFp) :
    decodeB width
        (pipeN (barrettLeafSpec q k width leaf limbStore)
          (modSwitchLeaves leaf n) oldDest xVal)
      = composeSpecs (modSwitchSpecs q k n) (decodeB width xVal) :=
  pipeN_realizes (decodeB width) (barrettLeafSpec q k width leaf limbStore)
    (modSwitchLeaves leaf n) (modSwitchSpecs q k n)
    (modSwitch_realized q k width hw leaf limbStore n) oldDest xVal

/-! ## §4  Montgomery-domain coefficient multiply — UNCONDITIONAL (strictly clean)

RNS BFV/CKKS coefficient arithmetic (and the ML-DSA / ML-KEM Montgomery multiply)
keeps coefficients in the Montgomery domain and multiplies them with
`montMul N R N'`.  The grounded Montgomery leaf `montMulLeafSpec` realizes that
binary kernel as a `KernelRealizes2` theorem for every input — the proved
`montMul_realizes_concrete` (in turn the verified base-256 `ℤ` codec round-trip
`decodeZ_encodeZ`).  Unlike the ML-KEM NTT route, this `.TFp`-carrier realizer
needs no `Fact (Nat.Prime ·)` instance and no primitive root, so it is strictly
axiom-clean (`{propext, Classical.choice, Quot.sound}`).  The side condition
`hfit` is the codec-fit residue-range condition (the Montgomery product is a
representable residue `0 ≤ montMul … < 256 ^ width`), NOT a kernel hypothesis. -/

/-- **GROUNDED Montgomery-domain coefficient multiply — UNCONDITIONAL (strictly
    axiom-clean).**

    A single RNS BFV/CKKS (or ML-DSA / ML-KEM) coefficient product in the
    Montgomery domain is `montMul N R N'`.  Over the proved concrete realizer
    `montMulLeafSpec` and the verified base-256 `ℤ` codec, the binary kernel
    realization holds for **every** input — the emitted Montgomery-multiply kernel
    decodes its two operands and computes exactly `montMul N R N'`, with **ZERO
    `KernelRealizes2` hypotheses**.  The realization is the proved
    `montMul_realizes_concrete` (in turn the codec round-trip `decodeZ_encodeZ`);
    strictly axiom-clean (no NTT primitive root / `Fact` instance involved).

    `hfit` is the codec-fit residue-range condition (`0 ≤ montMul … < 256 ^ width`,
    the representable-residue window) and `width ≤ 48` the digit-fit; NEITHER is a
    kernel hypothesis — the realizer computes `montMul N R N'` unconditionally.

    HONEST scope: this grounds the *computational backbone* — the emitted
    Montgomery coefficient-multiply kernel computes `montMul N R N'`.  It does NOT
    prove the FHE scheme's security, nor the correctness of the RNS / Montgomery
    representation choice (that the Montgomery constants `N`, `R`, `N'` are
    well-formed) — those are separate.  The only residual is the machine-code
    obligation for the Montgomery leaf — the owned-machine-code route, NOT a
    per-kernel hypothesis. -/
theorem grounded_fhe_montmul_coeff_realizes (N R N' : ℤ) (width : ℕ)
    (hw : width ≤ 48) (leaf : String) (limbStore : LimbStoreSpec)
    (hfit : ∀ aVal bVal : RustVal .TFp,
      0 ≤ montMul N R N' (decodeZ width aVal) (decodeZ width bVal) ∧
      montMul N R N' (decodeZ width aVal) (decodeZ width bVal) < 256 ^ width) :
    KernelRealizes2 (decodeZ width) (montMul N R N') leaf
      (montMulLeafSpec N R N' width leaf limbStore) :=
  montMul_realizes_concrete N R N' width hw leaf limbStore hfit

/-! ## §5  The combined FHE / threshold headline — the two strictly-clean
  `.TFp` backbones grounded

The strict FHE / threshold portfolio conjoins the two strictly axiom-clean
`.TFp`-carrier lattice-arithmetic backbones: the BFV/BGV modulus-switch Barrett
reduce chain and the Montgomery-domain coefficient multiply.  Both are
unconditional in their kernels and strictly axiom-clean
(`{propext, Classical.choice, Quot.sound}`).  The two ML-KEM NTT-route backbones
(§1, §2) are kept OUT of the strict portfolio: they carry the two ML-KEM-root
`native_decide` axioms intrinsic to the `.TPolyMod 3329 256` carrier (the same
axioms as the in-repo reference `grounded_mlkem_matvec_realizes`), exactly as
`GroundedMpcZk` keeps its `native_decide`-carrying permutation path out of its
strict portfolio and grounds the Merkle backbone through a strictly clean
conjunct.  Each conjunct grounds a *computational backbone*, not an FHE /
threshold security property. -/

/-- **THE FHE / THRESHOLD HEADLINE — two strictly axiom-clean backbones, ZERO
    kernel hypotheses.**

    The two strictly axiom-clean `.TFp`-carrier FHE / threshold lattice-arithmetic
    backbones conjoined:

    * the BFV/BGV modulus-switch / rescale Barrett reduce chain (`pipeN` of `n`
      `barrettCondsub q k` coefficient reductions), and
    * the Montgomery-domain coefficient multiply (`montMul N R N'` as a
      `KernelRealizes2`),

    each with **ZERO kernel hypotheses** — every per-step realization is a proved
    concrete realizer (`barrett_realizes_concrete`, `montMul_realizes_concrete`),
    in turn a verified base-256 codec round-trip.  Both conjuncts are strictly
    axiom-clean (`{propext, Classical.choice, Quot.sound}`).

    The two ML-KEM NTT-route backbones (`grounded_fhe_ctmult_realizes`,
    `grounded_threshold_combine_realizes`) ground the iterated NTT-domain
    polynomial-multiply backbone but inherit the two ML-KEM-root `native_decide`
    axioms intrinsic to the `.TPolyMod 3329 256` carrier (see the §1/§2 AXIOM
    NOTEs and the module Axioms section); they are therefore kept OUT of this
    strict portfolio, mirroring `GroundedMpcZk`.

    HONEST scope: each conjunct grounds the *computational backbone* — that the
    emitted Barrett-reduce / Montgomery-multiply kernel pipeline computes its
    arithmetic spec.  It does NOT prove the FHE / threshold security (FHE SEMANTIC
    SECURITY under RLWE, homomorphic-multiply / modulus-switch NOISE-GROWTH
    correctness, threshold-decryption PRIVACY / ROBUSTNESS, distributed-KeyGen
    SIMULATABILITY), which are separate assumption-bearing results.  The only
    residuals are the per-kernel machine-code obligations (owned-emit route). -/
theorem grounded_fhe_threshold_portfolio (limbStore : LimbStoreSpec)
    (q k width : ℕ) (hw : width ≤ 48) (leaf montLeaf : String) (n : ℕ)
    (N R N' : ℤ)
    (hfit : ∀ aVal bVal : RustVal .TFp,
      0 ≤ montMul N R N' (decodeZ width aVal) (decodeZ width bVal) ∧
      montMul N R N' (decodeZ width aVal) (decodeZ width bVal) < 256 ^ width)
    (reduceOldDest reduceXVal : RustVal .TFp) :
    -- BFV/BGV modulus-switch Barrett reduce chain: grounded, only codec fit.
    decodeB width
        (pipeN (barrettLeafSpec q k width leaf limbStore)
          (modSwitchLeaves leaf n) reduceOldDest reduceXVal)
      = composeSpecs (modSwitchSpecs q k n) (decodeB width reduceXVal)
    ∧
    -- Montgomery-domain coefficient multiply: grounded, only codec-fit residue range.
    KernelRealizes2 (decodeZ width) (montMul N R N') montLeaf
      (montMulLeafSpec N R N' width montLeaf limbStore) :=
  ⟨grounded_bfv_modswitch_realizes q k width hw leaf limbStore n
     reduceOldDest reduceXVal,
   grounded_fhe_montmul_coeff_realizes N R N' width hw montLeaf limbStore hfit⟩

end CatCrypt.Crypto.SecureCompilation.GroundedFheThreshold
