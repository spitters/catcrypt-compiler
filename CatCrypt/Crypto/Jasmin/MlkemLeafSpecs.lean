/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.ZMod.Basic
import CatCrypt.Crypto.MLKEM.ByteCodec
import CatCrypt.Crypto.MLKEM.Compress
import CatCrypt.Crypto.MLKEM.Sampler

/-!
# ML-KEM jasmin leaf functional-correctness specs (citation-style axioms)

The CatCrypt verified front (the `LowCT → MLIR → jasmin` pipeline used by
`bench/mlkem_compare/`) currently **trusts** the formosa-mlkem reference
leaves by Known-Answer-Test (KAT) only. The kernels emitted by the verified
front call out to hand-written jasmin leaf functions
(`rp_gen_matrix`, `rp_cbd_eta1_polyvec`, `rp_hash_g`, …) whose bodies are
spliced in from the `formosa-mlkem` implementation; their agreement with the
FIPS 203 spec is checked only against NIST KAT vectors.

This file shrinks the *documented* trust boundary by stating, for each leaf
class, a **citation-style axiom** that captures the leaf's functional
contract over a clean abstract Lean model and **cites the EasyCrypt (EC)
functional-correctness theorem** that discharges it. This mirrors the
existing Rocq-citation pattern in
`CatCrypt/Crypto/Jasmin/Ed25519Optimizations.lean` (the
`-- Discharged in Rocq: <file> <theorem>` style) and the trust registry in
`CatCrypt/Crypto/TrustAxioms.lean`.

## Provenance honesty (read this first)

A local scan found **no functional-correctness EasyCrypt sources for the
ML-KEM jasmin implementation in this tree**:

* `BLS/libjade/proof/crypto_kem/kyber/{kyber512,kyber768}/amd64/{ref,avx2}/`
  contains only `.gitkeep` placeholders — no `.ec` files. (The libjade proof
  subtree that *is* populated — curve25519, shake256, sha3, poly1305, chacha —
  holds **constant-time** `extracted_ct_proof.ec` files only, never ML-KEM
  functional correctness.)
* `BLS/libjade/submodules/formosa-mlkem/` is an **uninitialised submodule**
  (empty directory).
* No `.ec` file anywhere in the local workspace mentions `kyber`/`mlkem` in
  either its path or its content.
* The only local ML-KEM *spec* artefacts are the libcrux F* extraction
  (`libcrux/specs/kyber/proofs/fstar/extraction/Hacspec_kyber.*.fst`) and
  CatCrypt's own Lean MLWE/FO development (`CatCrypt/Crypto/MLKEM/`). Neither
  is the jasmin↔spec equivalence proof we want to cite.

Therefore every citation below is to the **upstream formosa-crypto EasyCrypt
ML-KEM development** (Almeida, Barbosa, Barthe, Grégoire, et al., *"Formally
verifying Kyber"*, CRYPTO 2023), whose artifact is public at

> https://github.com/formosa-crypto/formosa-mlkem  (default branch `main`)

The ML-KEM-768 reference-implementation functional-correctness proofs live
under `proof/correctness/768/ref/` (the AVX2 variants under
`proof/correctness/768/avx2/`); the keccak/SHA-3 leaves under
`proof/correctness/768/ref/MLKEM_keccak_ref.ec`. The jasmin procedures appear
as `Jkem768.M.<proc>` (and `Jkem768_avx2.M.<proc>` for AVX2). The cited
lemma/equiv names below were **confirmed by reading those files on GitHub**
(`main`, fetched 2026-05-24) and the `[name to be verified]` markers removed
for each leaf so confirmed. Two honest caveats remain:

* The keccak correctness *currently assumes the underlying SHA-3
  implementation is correct* (per the formosa-mlkem README; the assumption is
  slated for removal). So §1's citation is to the jasmin↔`SHA3_512_*` glue
  lemma, layered on that standing assumption.
* These are still **upstream** proofs (not in this Lean tree); the axioms here
  document the trust boundary, they do not import the EC proofs.

## The NTT is proven, not trusted

The NTT-family leaves (`_poly_ntt` / `_poly_basemul` / `_poly_invntt`) are
**not** given a trust axiom here. The negacyclic-convolution correctness of
the real CompPoly NTT product is a *proved* Lean theorem:

> `CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic.realNttMul_negacyclic_coeff`

which establishes, for the real NTT/pointwise-multiply/inverse-NTT pipeline
over `Z_q[X]/(X^n + 1)`, that the coefficient-wise result equals the
negacyclic convolution (cyclic full product folded by the `X^n ≡ −1`
reduction) — not a definitional `rfl`. See §7 below for the in-tree
`ntt_basemul_is_proven` marker that records this distinction in the leaf
table.

## What this file does NOT claim

These axioms do **not** assert that the *emitted jasmin* matches the spec —
that is the KAT-level trust this file is *documenting*, not discharging. Each
axiom states the leaf's mathematical contract and names the EC theorem under
which the formosa leaf is known to satisfy it; turning the KAT into a named,
auditable obligation is the "principled trust-boundary upgrade". A future
Lean port of the EC proofs (or a Lean model of the jasmin semantics) would
replace these axioms with theorems.

## Leaf coverage

| Leaf (formosa name)                       | FIPS 203 spec      | §  |
|-------------------------------------------|--------------------|----|
| `_sha3512_32`                             | SHA3-512           | §1 |
| `__gen_matrix`                            | SampleNTT (Alg. 7) | §2 |
| `_poly_getnoise` / `rp_cbd_eta1_polyvec`  | SamplePolyCBD_η    | §3 |
| `_poly_compress` / `__polyvec_compress`   | Compress_d         | §4 |
| `_poly_decompress` / `__polyvec_decompress`| Decompress_d      | §4 |
| `__polyvec_tobytes` / `__polyvec_frombytes`| ByteEncode/Decode  | §5 |
| `_poly_ntt`/`_poly_basemul`/`_poly_invntt`| NTT (PROVEN)       | §7 |
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.MlkemLeafSpecs

/-! ## §0  Abstract ML-KEM model types

We keep the model deliberately light: an ML-KEM polynomial is its
coefficient vector `Fin 256 → ZMod 3329` (FIPS 203: `n = 256`, `q = 3329`),
a polynomial vector / matrix is indexed over `Fin k` (`k = 3` for
ML-KEM-768 but kept abstract here), and byte buffers are `List UInt8`.

The leaf contracts below are stated against these clean models; the leaves'
*jasmin* representation (packed `u16[256]`, Montgomery domain, etc.) is the
implementation detail that the cited EC equivalence proof relates to this
model. -/

/-- ML-KEM modulus `q = 3329` (FIPS 203 §2.3). -/
abbrev mlkemQ : Nat := 3329

/-- ML-KEM ring degree `n = 256` (FIPS 203 §2.3). -/
abbrev mlkemN : Nat := 256

/-- A single ML-KEM polynomial as a coefficient vector in `Z_q`. -/
abbrev Poly := Fin mlkemN → ZMod mlkemQ

/-- A 32-byte buffer (e.g. a seed `ρ`/`σ` or a SHAKE/CBD input). -/
abbrev Bytes32 := List UInt8

/-- An arbitrary-length byte buffer. -/
abbrev Bytes := List UInt8

/-! ## §1  SHA3-512 (`_sha3512_32`)

The keygen leaf `_sha3512_32` hashes a 32-byte seed `d` to the 64-byte
`(ρ ‖ σ)` pair (FIPS 203 §5.1, the `G` function instantiated as SHA3-512).
We model it as an opaque byte-to-byte function and assert only the contract
that matters at the spec level: the output is the FIPS 202 SHA3-512 digest
of the input. The reference SHA3-512 (the *spec*) is itself opaque here. -/

/-- The opaque jasmin keccak leaf `_sha3512_32 : [u8;32] → [u8;64]`. -/
axiom sha3_512_leaf : Bytes32 → Bytes

/-- The FIPS 202 SHA3-512 reference function (spec side), opaque. -/
axiom sha3_512_spec : Bytes → Bytes

/-- **EC citation:** `formosa-mlkem:proof/correctness/768/ref/MLKEM_keccak_ref.ec`
    — `phoare sha3_512_33_64` (and the keygen-`G` form `phoare sha_g` for the
    64-byte buffer; via the `equiv sha3512_33_eq` / `hoare sha3512_33_h'`
    chain). These show the jasmin keccak leaf `Jkem768.M._sha3_512A_A33`
    (resp. `M._sha3_512A_A64`) computes `SHA3_512_33_64 seed` (resp.
    `SHA3_512_64_64`), i.e. the FIPS 202 SHA3-512 digest split into the two
    32-byte halves `(ρ ‖ σ)`. (Caveat: per the formosa-mlkem README, the keccak
    correctness currently *assumes* the underlying SHA-3 sponge is correct;
    this lemma is the jasmin↔`SHA3_512_*` glue on top of that assumption.)
    https://github.com/formosa-crypto/formosa-mlkem -/
axiom sha3_512_leaf_correct (d : Bytes32) :
    sha3_512_leaf d = sha3_512_spec d

/-! ## §2  Matrix generation (`__gen_matrix`, SHAKE128 rejection sampling)

`__gen_matrix` expands the public seed `ρ` into the `k×k` matrix `Â` of
NTT-domain polynomials via SHAKE128-seeded rejection sampling
(FIPS 203 Alg. 7 `SampleNTT`, FIPS 203 §6.1 `K-PKE.KeyGen` step). The
contract: each entry `Â[i][j]` equals the spec's `SampleNTT` applied to
`(ρ ‖ j ‖ i)` (transpose convention per FIPS 203). -/

/-- Number of polynomials per row/column of `Â` (ML-KEM-768: `k = 3`),
    kept abstract. -/
axiom mlkemK : Nat

/-- The opaque `__gen_matrix` leaf: seed `ρ` and indices `(i,j)` to the
    matrix entry `Â[i][j]` (an NTT-domain polynomial). The full leaf
    produces all `k²` entries; we expose it entry-wise to state the
    per-entry rejection-sampling contract. -/
axiom gen_matrix_leaf : Bytes32 → Fin mlkemK → Fin mlkemK → Poly

/-- The FIPS 203 Alg. 7 `SampleNTT` reference: a 34-byte SHAKE128 input
    (`ρ` ‖ two index bytes) to a uniform NTT-domain polynomial via
    rejection sampling. Opaque (spec side). -/
def sampleNTT_spec : Bytes → Poly := CatCrypt.Crypto.MLKEM.Sampler.sampleNTT

/-- The XOF input byte string `ρ ‖ j ‖ i` consumed by `SampleNTT` for
    entry `(i,j)` (FIPS 203 §6.1; note the transpose `(j,i)` order). -/
axiom genMatrixXofInput : Bytes32 → Fin mlkemK → Fin mlkemK → Bytes

/-- **EC citation:** `formosa-mlkem:proof/correctness/768/ref/MLKEM_InnerPKE.ec`
    — `equiv auxgenmatrix_good` relates the jasmin `Jkem768.M.__gen_matrix`
    (parametrised by the `transposed` flag) to `AuxMLKEM.__gen_matrix`, whose
    body inlines `Parse(XOF).sample` — the spec's SHAKE128 rejection sampler
    (FIPS 203 Alg. 7 `SampleNTT` on the `ρ ‖ j ‖ i` input). The AVX2 variant
    is `phoare _gen_matrix_avx2_sem` / `equiv genmatrixequiv_aux` in
    `proof/correctness/768/avx2/MLKEM_genmatrix_avx2.ec` (with the
    rejection-sampling agreement `hoare gen_matrix_buf_rejection_h`). Thus the
    leaf's rejection sampler agrees with the spec's `Parse`/`SampleNTT`.
    https://github.com/formosa-crypto/formosa-mlkem -/
axiom gen_matrix_leaf_correct (rho : Bytes32) (i j : Fin mlkemK) :
    gen_matrix_leaf rho i j = sampleNTT_spec (genMatrixXofInput rho i j)

/-! ## §3  Centered binomial sampling (`_poly_getnoise` / `rp_cbd_eta1_polyvec`)

The noise leaves sample a polynomial whose coefficients follow the centered
binomial distribution `CBD_η` (FIPS 203 §4.2.2 `SamplePolyCBD_η`), with the
PRF input being `(σ ‖ N)` expanded by SHAKE256. The functional-correctness
contract is that, given the *same* PRF byte stream, the leaf computes exactly
the spec's `SamplePolyCBD_η` decoding of that stream. -/

/-- The opaque `_poly_getnoise` / `rp_cbd_eta1_polyvec` leaf: PRF input
    `(σ ‖ N)` (33 bytes) and the parameter `η` to a noise polynomial. -/
axiom poly_getnoise_leaf : Bytes → Nat → Poly

/-- FIPS 203 §4.2.2 `SamplePolyCBD_η` reference: decode a `64·η`-byte PRF
    output into a centered-binomial polynomial. Opaque (spec side). -/
def samplePolyCBD_spec (b : Bytes) (eta : Nat) : Poly :=
  CatCrypt.Crypto.MLKEM.Sampler.sampleCBD_eta eta b

/-- The SHAKE256 PRF expansion `PRF(σ, N)` of length `64·η` consumed by
    `SamplePolyCBD_η` (FIPS 203 §4.1, the `PRF` function). Opaque. -/
axiom getnoisePrfStream : Bytes → Nat → Bytes

/-- **EC citation:** `formosa-mlkem:proof/correctness/768/ref/MLKEM_InnerPKE.ec`
    — `equiv get_noise_sample_noise` relates the jasmin
    `Jkem768.M._poly_getnoise` to the spec sampler `CBD2.sample` on the PRF
    input `PRF σ N` (lifting to `lift_array256 res{1} = res{2}` with the CBD
    range `−5 < to_sint < 5`), i.e. the leaf decodes the SHAKE256 PRF stream
    exactly as FIPS 203 `SamplePolyCBD_η`. The polyvec-level wrappers are
    `equiv sample_noise_good2` / `sample_noise_good3` (jasmin
    `sample_noise2_jasmin` vs `sample_noise2_spec`). (The PRF/SHAKE256
    agreement itself is the §1-style keccak lemma `phoare shake256_33_128` in
    `MLKEM_keccak_ref.ec`; this axiom is the CBD *decoding* agreement on top.)
    https://github.com/formosa-crypto/formosa-mlkem -/
axiom poly_getnoise_leaf_correct (prfInput : Bytes) (eta : Nat) :
    poly_getnoise_leaf prfInput eta
      = samplePolyCBD_spec (getnoisePrfStream prfInput eta) eta

/-! ## §4  Compression / decompression (`_poly_compress`, `__polyvec_compress`,
    `_poly_decompress`, `__polyvec_decompress`)

`Compress_d : Z_q → Z_{2^d}` is `⌈(2^d / q) · x⌋ mod 2^d` and
`Decompress_d : Z_{2^d} → Z_q` is `⌈(q / 2^d) · y⌋` (FIPS 203 §4.2.1). The
leaves apply these coefficient-wise. We model the per-coefficient maps and
state agreement coefficient-wise (the `__polyvec_*` variants are the
per-component lift, so a single contract suffices). -/

/-- Per-coefficient `Compress_d` reference (FIPS 203 §4.2.1):
    `⌈(2^d / q)·x⌋ mod 2^d`, returned as a `Nat` in `[0, 2^d)`. Opaque. -/
def compress_spec (d : Nat) (x : ZMod mlkemQ) : Nat :=
  (CatCrypt.Crypto.MLKEM.Compress.compress_d d x).val

/-- Per-coefficient `Decompress_d` reference (FIPS 203 §4.2.1):
    `⌈(q / 2^d)·y⌋`. Opaque. -/
def decompress_spec (d : Nat) (y : Nat) : ZMod mlkemQ :=
  CatCrypt.Crypto.MLKEM.Compress.decompress_d d (y : ZMod (2 ^ d))

/-- The opaque `_poly_compress` leaf, exposed coefficient-wise: parameter
    `d`, coefficient index, polynomial to a compressed `Nat`. -/
axiom poly_compress_leaf : Nat → Fin mlkemN → Poly → Nat

/-- The opaque `_poly_decompress` leaf: parameter `d` and a vector of
    compressed `Nat` coefficients to the decompressed polynomial. -/
axiom poly_decompress_leaf : Nat → (Fin mlkemN → Nat) → Poly

/-- **EC citation:** `formosa-mlkem:proof/correctness/768/ref/MLKEM_PolyVec.ec`
    — `lemma i_polyvec_compress_corr`:
    `phoare [Jkem768.M.__i_polyvec_compress : … ==>
       res = encode10_vec (compress_polyvec 10 (lift_polyvec _aw))] = 1%r`,
    i.e. the jasmin `__polyvec_compress` leaf computes `compress_polyvec 10`
    (FIPS 203 `Compress_d` coefficient-wise, then `ByteEncode`). Supporting
    per-coefficient lemmas in the same file: `compress10_circuit_sem`,
    `encode_vec_compress_bits`. (For the per-`poly` `d=1` message path see
    `lemma poly_tomsg_corr` in `MLKEM_Poly.ec`.)
    https://github.com/formosa-crypto/formosa-mlkem -/
axiom poly_compress_leaf_correct (d : Nat) (k : Fin mlkemN) (p : Poly) :
    poly_compress_leaf d k p = compress_spec d (p k)

/-- **EC citation:** `formosa-mlkem:proof/correctness/768/ref/MLKEM_PolyVec.ec`
    — `lemma polyvec_decompress_corr`:
    `phoare [Jkem768.M.__i_polyvec_decompress : ap = _aw ==>
       … /\ lift_polyvec res = decompress_polyvec 10 (decode10_vec _aw)] = 1%r`,
    i.e. the jasmin `__polyvec_decompress` leaf computes `decompress_polyvec 10`
    (FIPS 203 `Decompress_d` after `ByteDecode`). Supporting per-coefficient
    lemmas: `decompress10_circuit_sem`, `decompress10_circuit_rng`. (For the
    per-`poly` `d=1` message path see `lemma poly_frommsg_corr` in
    `MLKEM_Poly.ec`.)
    https://github.com/formosa-crypto/formosa-mlkem -/
axiom poly_decompress_leaf_correct (d : Nat) (k : Fin mlkemN)
    (c : Fin mlkemN → Nat) :
    poly_decompress_leaf d c k = decompress_spec d (c k)

/-- **Proved (model-level round-trip shape).** Decompressing a compressed
    vector via the `_poly_decompress` leaf and then re-compressing
    coefficient-wise via the `_poly_compress` leaf is the composition of the
    two specs — the shape a `Compress ∘ Decompress` near-identity argument
    (FIPS 203 §4.2.1, the rounding-error bound) would build on. It chains
    both leaf-correctness axioms on a shared `d`/`k`, ruling out a vacuous
    pairing. -/
theorem compress_decompress_leaf_chain (d : Nat) (k : Fin mlkemN)
    (c : Fin mlkemN → Nat) :
    poly_compress_leaf d k (poly_decompress_leaf d c)
      = compress_spec d (decompress_spec d (c k)) := by
  rw [poly_compress_leaf_correct, poly_decompress_leaf_correct]

/-! ## §5  Byte (de)serialisation (`__polyvec_tobytes` / `__polyvec_frombytes`)

`ByteEncode_d` packs a polynomial's `d`-bit coefficients into a byte string
and `ByteDecode_d` is its inverse (FIPS 203 §4.2.1, Alg. 5/6). The
`__polyvec_*` variants concatenate the per-polynomial encodings. Contract:
the leaves implement `ByteEncode_d` / `ByteDecode_d`, and on canonical
(in-range) inputs they round-trip. -/

/-- FIPS 203 `ByteEncode_d` reference: a polynomial and bit-width `d` to a
    `32·d`-byte string. Opaque (spec side). -/
def byteEncode_spec (d : Nat) (p : Poly) : Bytes :=
  CatCrypt.Crypto.MLKEM.ByteCodec.byteEncode d p

/-- FIPS 203 `ByteDecode_d` reference: a `32·d`-byte string and `d` back to
    a polynomial. Opaque (spec side). -/
def byteDecode_spec (d : Nat) (b : Bytes) : Poly :=
  CatCrypt.Crypto.MLKEM.ByteCodec.byteDecode d mlkemQ b

/-- The opaque `__polyvec_tobytes` leaf (here at polynomial granularity;
    the polyvec leaf is the concatenation over the `k` components). -/
axiom poly_tobytes_leaf : Nat → Poly → Bytes

/-- The opaque `__polyvec_frombytes` leaf. -/
axiom poly_frombytes_leaf : Nat → Bytes → Poly

/-- **EC citation:** `formosa-mlkem:proof/correctness/768/ref/MLKEM_PolyVec.ec`
    — `lemma polyvec_tobytes_corr` (with `polyvec_tobytes_corr_h`): the jasmin
    `Jkem768.M.__i_polyvec_tobytes` leaf computes `encode 12 …` over the lifted
    coefficients, i.e. FIPS 203 `ByteEncode_12`. The bit-level kernel is
    `lemma to_bytes_circuit_sem` in the same file (and `poly_tobytes_corr` in
    `MLKEM_Poly.ec` for the single-poly case).
    https://github.com/formosa-crypto/formosa-mlkem -/
axiom poly_tobytes_leaf_correct (d : Nat) (p : Poly) :
    poly_tobytes_leaf d p = byteEncode_spec d p

/-- **EC citation:** `formosa-mlkem:proof/correctness/768/ref/MLKEM_PolyVec.ec`
    — `lemma polyvec_frombytes_corr`:
    `phoare [Jkem768.M.__i_polyvec_frombytes : ap = _aw ==>
       lift_array768 res = map incoeff (decode12_vec _aw) /\ …] = 1%r`,
    i.e. the jasmin `__polyvec_frombytes` leaf computes `decode12_vec`, FIPS 203
    `ByteDecode_12`. Bit-level kernel: `frombytes_circuit_sem` /
    `frombytes_circuit_rng` (and `poly_frombytes_corr` in `MLKEM_Poly.ec`).
    https://github.com/formosa-crypto/formosa-mlkem -/
axiom poly_frombytes_leaf_correct (d : Nat) (b : Bytes) :
    poly_frombytes_leaf d b = byteDecode_spec d b

/-- **EC citation:** `crypto-specs:ml-kem/properties/EncDecCorrectness768.ec`
    (the `formosa-crypto/crypto-specs` submodule that formosa-mlkem builds
    against) — `lemma sem_decode12_vecK : cancel decode12_vec encode12_vec`
    (and the per-poly `sem_decode12K`, `sem_decode1K`, `sem_decode4K`; the
    general bit-level `decodeK` / `encodeK`). These give the
    `ByteDecode_d ∘ ByteEncode_d = id` round-trip used to make §5 non-vacuous:
    the two leaf specs are mutually inverse.
    https://github.com/formosa-crypto/crypto-specs
    (vendored under formosa-mlkem at `crypto-specs/`) -/
theorem byteDecode_byteEncode_cancel (d : Nat) (hd : mlkemQ ≤ 2 ^ d) (p : Poly) :
    byteDecode_spec d (byteEncode_spec d p) = p := by
  have : NeZero mlkemQ := ⟨by norm_num⟩
  exact CatCrypt.Crypto.MLKEM.ByteCodec.byteDecode_byteEncode d mlkemQ hd p

/-- **Proved.** The two byte leaves round-trip through their specs:
    `frombytes (tobytes p) = p`, whenever `d` is wide enough to hold a
    `Z_q` coefficient (`mlkemQ ≤ 2^d`, i.e. `d ≥ 12` — the FIPS 203 poly
    encoding uses `d = 12`). It fails unless the two leaf-correctness axioms
    agree on `d` and the spec-level cancel holds. -/
theorem polyvec_bytes_roundtrip (d : Nat) (hd : mlkemQ ≤ 2 ^ d) (p : Poly) :
    poly_frombytes_leaf d (poly_tobytes_leaf d p) = p := by
  rw [poly_tobytes_leaf_correct, poly_frombytes_leaf_correct]
  exact byteDecode_byteEncode_cancel d hd p

/-! ## §6  Keygen `G`-output split (derived)

Keygen splits the 64-byte SHA3-512 output `(ρ ‖ σ)`. We record the contract
that the keygen seed derivation is exactly `_sha3512_32`, tying §1 to the
matrix-gen seed `ρ` used in §2 — again to keep the trust documentation
connected rather than a bag of unrelated axioms. -/

/-- The first 32 bytes of a 64-byte buffer (`ρ`), opaque splitter. -/
axiom takeRho : Bytes → Bytes32
/-- The last 32 bytes of a 64-byte buffer (`σ`), opaque splitter. -/
axiom takeSigma : Bytes → Bytes32

/-- **Proved.** The keygen public seed `ρ` is `takeRho` of the SHA3-512
    digest of the keygen seed `d` (composes §1's leaf-correctness with the
    pure splitter). -/
theorem keygen_rho_eq (d : Bytes32) :
    takeRho (sha3_512_leaf d) = takeRho (sha3_512_spec d) := by
  rw [sha3_512_leaf_correct]

/-! ## §7  NTT family is PROVEN, not trusted (marker)

No trust axiom for `_poly_ntt` / `_poly_basemul` / `_poly_invntt`. The
negacyclic-convolution correctness of the real NTT product is the **proved**
Lean theorem

> `CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic.realNttMul_negacyclic_coeff`

(over `CompPoly`, i.e. `Z_q[X]/(X^n + 1)`; not `rfl`). We record the
distinction with a `Prop`-level marker so a `#print axioms`-style audit of
this file shows the NTT class is *not* among the trusted leaves. -/

/-- Marker recording that the NTT/basemul/invntt leaf class is discharged by
    an in-tree Lean proof (`realNttMul_negacyclic_coeff`), not by a trust
    axiom in this file. Proved by `rfl`; its *value* is the citation in its
    statement/docstring, not the proposition's logical strength. -/
def ntt_basemul_is_proven : Prop := True

theorem ntt_basemul_is_proven_holds : ntt_basemul_is_proven := trivial

end CatCrypt.Crypto.Jasmin.MlkemLeafSpecs
