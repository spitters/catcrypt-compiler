# Primitive coverage index

Each row maps a cryptographic primitive with kernels in this package to the Lean
modules that build or emit it, the theorems about those kernels, and the provenance
class of the kernel. Paths are relative to the repository root; `SC/` abbreviates
`CatCrypt/Crypto/SecureCompilation/`. `git grep -n 'theorem <name>'` locates each
theorem.

## Provenance classes

- Front-generated, denotation proved: a front (`reifyLowCT%`,
  `translateDialectControl`, `compileFromHax`, `buildOrchCom`) produces the `Com`
  from a source program, and a theorem equates its denotation with a specification
  for every input.
- Front-generated, sample-checked: a front produces the `Com`; an evaluation on a
  fixed input list checks agreement with a reference function on those inputs.
- Front-generated, structural: a front produces the `Com`; the checks cover
  lowering success, op vocabulary and output layout.
- Builder `Com`: the `Com` is written in Lean as de Bruijn chains or by builder
  functions. The row names its denotation theorems.
- String-rendered: Lean `String` templates produce the emitted text; substring tests
  check its shape.
- Orchestration over leaves: the kernel sequences calls to external leaves. The
  theorems state which leaves are called on which arguments, under a leaf oracle.
- Trusted leaf: an instruction or called routine whose semantics is assumed.

## Symmetric family

| Primitive | Modules | Theorems | Provenance |
|---|---|---|---|
| AES-128 | `SC/VIR/AesRoundCatCryptEmit.lean`; `SC/X86Backend/Aes128CtrVsimdEmit.lean` | `xtimeW_eq_spec`, `mul3W_eq_spec`: the GF(2⁸) helpers equal `AES128.xtime`/`AES128.mul3`. `keyExpandRoundCom_denote`, `ecbCom_denote`: for every input, the key-schedule and ECB `Com`s equal `keyExpandRoundSpec`/`ecbSpec` over the `AESKEYGENASSIST`/`AESENC` op denotations. | Key schedule and ECB body: builder `Com`. CTR loop and ABI: string-rendered. The AES round is `VAESENC`, a trusted leaf. |
| GF(2¹²⁸) / GHASH | `SC/VIR/Gf2Dialect.lean`; `SC/VIR/Gf2Aggregate.lean`; `SC/VIR/VPClmulEmit.lean` | `mulReducedBlock_denote`: the reduced carry-less multiply block. `ghashJ_denote`: the GHASH loop lowered to `jasminDialect`. `ghashAggJ_denote_ghashFold`: the four-block aggregated loop equals the GHASH fold. `vpclmulqdq_eq_polyMul`: the `VPCLMULQDQ` op denotation is the carry-less product. | Template over `gf2Dialect` lowered by `gf2ToJasmin`, denotation level. |
| HMAC / HKDF | `SC/VIR/HmacHkdfEmit.lean` | `xorPadCom_denote`, `xorPadComW_denote`: the XOR-pad output word. `expandLoop_denote_eq`, `expandSkelLoop_denote_eq`: running the expand loop equals the `Com` denotation under `LeafAgrees`. `hmac_ipad_lowers`, `hmac_opad_lowers`: the pad expression lowers through the front. | XOR pad: builder `Com`. HKDF-Expand step: the `hkdf_expand_step` leaf, trusted. |
| Keccak / SHAKE | `SC/VIR/KeccakEmit.lean`; `SC/VIR/KeccakFipsAscent.lean`; `SC/VIR/KeccakRoundCatCryptEmit.lean`; `SC/VIR/Shake256SpongeEmit.lean` | `KeccakFipsAscent.keccakF1600Com_denote_spec`: for every 25-lane state, the denotation of `keccakF1600Com` is lane 24 of the 24-round FIPS 202 permutation; `keccak_emit_state_fips` states all 25 lanes of the slot-map model; `toKState_round` identifies the round with `Primitives.Keccak.keccakRound`. `shake256Body_front_sourced`: the sponge body is the rendering of its step schedule. | Permutation: builder `Com` with a universal denotation theorem, lowered by `Com.toLprogPhysAbi` (`SC/VIR/KeccakLinearMain.lean`). SHAKE256 sponge: rendered from the `SpStep` schedule around the permutation leaf. |
| Poly1305 | `SC/VIR/Poly1305Com.lean`; `SC/VIR/Poly1305RtLoopCom.lean`; `SC/VIR/ChaChaPolyEmit.lean`; `SC/X86Backend/Poly1305Kernel.lean` | `poly1305MacLowered_isSome`, `macRtProg_isSome`, `poly1305_is_purearith_only`: the front lowers the MAC and emits pure arithmetic. `poly1305_dot`, `poly1305_mac_dot`: the MAC as a polynomial sum over `ZMod (2¹³⁰−5)`. | `Poly1305Com`: front-generated, structural. `ChaChaPolyEmit`, `Poly1305Kernel`: string-rendered. |
| SHA-256 | `SC/VIR/Sha2Emit.lean`; `SC/VIR/Sha256CompressCatCryptEmit.lean`; `SC/VIR/Sha256RoundCatCryptEmit.lean` | `sha256_sigma0_jasmin_denote`, `sha256_sigma1_jasmin_denote`, `sha256_ch_jasmin_denote`, `sha256_maj_jasmin_denote`: the lowered mixing functions equal their `Sha256Verified` references for every input. `sha256Compress_catcrypt_denote`: the compression built from the mixing `Com`s equals `sha256CompressSpec`. | Mixing functions: builder `Com`s with universal denotation theorems. `bench/sha2_linear_compare/sha256_owned_body.s` is lowered from `Sha2Emit.compressCom sha256Spec`. |
| SHA-512 | `SC/VIR/Sha2Emit.lean`; `SC/VIR/Sha512CompressCatCryptEmit.lean`; `SC/VIR/Sha512RoundCatCryptEmit.lean` | `sha512_sigma0_jasmin_denote`, `sha512_sigma1_jasmin_denote`, `sha512_ch_jasmin_denote`, `sha512_maj_jasmin_denote`; `sha512Compress_catcrypt_denote`, `sha512RoundCat_eq`, `runRoundsCat_eq`, as for SHA-256. | As for SHA-256, with `bench/sha2_linear_compare/sha512_owned_body.s`. |
| BLAKE3 `G` step | `SC/CompileFromHaxBlake3.lean` | `blake3GA_compiles` … `blake3GD_compiles`: `compileFromHax` returns a `Com jasminDialect` whose denotation equals the matching output word of `blake3GSpec` for every input (`compileFromHax_meets_spec`). | Front-generated, denotation proved, from a hax `ImpExpr` source. |

## Field, curve and pairing family

| Primitive | Modules | Theorems | Provenance |
|---|---|---|---|
| BN254 G1 affine point add | `CatCrypt/Crypto/Pairing/BN254GroupEmit.lean`; `CatCrypt/Crypto/Pairing/BN254GroupDenote.lean` | `lamCom_denoteWith`, `bn254AddxCom_denoteWith`, `bn254AddyCom_denoteWith`: for every leaf oracle satisfying `FieldLeafAgrees prims`, the slope, `x₃` and `y₃` kernels compute the matching composition of `prims.mul`/`sub`/`inv`; `bn254FieldOracle_agrees` shows such an oracle exists. | Orchestration over leaves, front-generated by `buildOrchCom`. Field leaves: `SC/X86Backend/Bn254MontMulKernel.lean` and AUCurves routines, trusted. |
| BLS12-377 field and pairing orchestration | `CatCrypt/Crypto/Pairing/Bls12_377Emit.lean`; `CatCrypt/Crypto/Pairing/Bls12_377Denote.lean` | `fieldAddCom_denote`, `fieldMulCom_denote`, `fieldInvCom_denote`, `pairingCom_denote`, `fp12MulCom_denote`, `pairingProductCom_denote` and siblings: under the leaf agreements, each kernel computes the matching field of the byte-level record `Bls377Primitives`. | Orchestration over leaves, front-generated by `buildOrchCom`; emitted as `bench/bls12_377_compare/gen_com/bls12_377_orch_owned.s`. Field arithmetic and pairing: AUCurves routines, trusted. |
| BabyBear Montgomery multiply, Poseidon2 S-box `x^7` | `SC/ThirToComFront.lean`; `SC/ThirSboxRange.lean` | `montMul_via_thirDialect`, `sbox_via_thirDialect`: for every `u64` input, the lowered `Com jasminDialect` denotes `montMulSpec64` / `sboxSpec64`. `montMulSpec64_exact`: the REDC identity under its range condition. `sboxSpec64_modEq`: `sboxSpec64 x · 2^192 ≡ x^7 (mod p)` for `x ≤ 1756563332`. | Builder `Com thirDialect`, lowered by `lowerThir`; universal denotation theorems. |

## Lattice and post-quantum family

| Primitive | Modules | Theorems | Provenance |
|---|---|---|---|
| HAWK-style negacyclic multiply, degree-16 tile over `Z/1024[x]/(x¹⁶+1)` | `SC/VIR/HawkMulEmit.lean`; `SC/VIR/HawkMulComDenoteTie.lean` | `HawkMulComDenoteTie.hawkMulCom_denote_spec`: the model `hawkMulCom` computes the negacyclic product for every input pair. `hawk_denote_spec`: the deployed front program agrees with `refCoeff` on the sample pairs. | Front-generated, sample-checked. |
| HAWK-512 NTT butterflies and pointwise multiply | `SC/X86Backend/HawkNttEmit.lean`; `SC/X86Backend/HawkPointwiseEmit.lean` | `nttBflyLowered_isSome`, `inttBflyLowered_isSome`, `pwComL_isSome`: the front lowers each kernel. `pwProgS_denote`: the rolled pointwise loop on a sample stream. | Front-generated, structural; pointwise loop sample-checked. |
| NTRU-HRSS-style cyclic multiply, degree-16 tile over `Z/8192[x]/(x¹⁶−1)` | `SC/VIR/Ntruhrss701MulEmit.lean`; `SC/VIR/Ntruhrss701KaratsubaEmit.lean` | `ntru_denote_spec`: agreement on the sample pairs. `karaLowered_isSome`, `kara_mul_count_192`: the Karatsuba variant lowers with 192 multiplies. | Front-generated, sample-checked. |
| ML-KEM-768 and ML-DSA-65 4-way butterfly stages | `SC/VIR/LatticeNttEmit.lean`; `SC/MLIR/VectorDialect/MldsaNtt4WayVec.lean`; `SC/VIR/MlkemRaEmit.lean`; `SC/VIR/MlkemNttFullResidentEmit.lean` | `mlkem_ntt_4way_denotation_preserves`, `mldsa_ntt_4way_denotation_preserves`: the instruction list `ntt4wayBody` renders line for line to the emitted body, and its run writes, for each of the 8 stages and each lane, the Cooley–Tukey butterfly in wrapping 16-bit / 32-bit arithmetic. `mlkem_ntt_4way_ra_emit_denotation_preserves`: the same for every register allocation with distinct slot names. `mlkem_ntt_full_resident_denotation_preserves`: the fused and the three-loop full-transform bodies leave the same polynomial array. | String-rendered, with a render theorem to `ntt4wayBody` and the lane-level semantics `runNtt4way`. |
| FN-DSA verify subtraction and CDT base sampler | `SC/VIR/FndsaEmit.lean`; `SC/VIR/FndsaEmit/Sampler.lean` | `Sampler.fixedPointCDTGaussian_range`: the Lean sampler returns a value in `[-19, 19]`. `fndsa_verify_lane_map`: the lane map is per-lane application. | String-rendered. |

## Proof-system orchestration

| Primitive | Modules | Theorems | Provenance |
|---|---|---|---|
| Plonky3 prover layers | `CatCrypt/Crypto/Jasmin/Plonky3Reflect.lean`, `Plonky3AirReflect.lean`, `Plonky3FriReflect.lean`, `Plonky3LdeReflect.lean`, `Plonky3ProveReflect.lean`; `SC/VIR/Plonky3OrchLoopsEmit.lean`, `SC/VIR/Plonky3PaddingFreeSpongeEmit.lean`, `SC/VIR/Plonky3SerializeEmit.lean` | `orchLoopFundef_eq_buildOrchLoop`, `leWriterFundef_body_eq`: structural equalities of the rendered loops. | Orchestration over axiomatized leaves, as `LowCT` bodies. |
| Bulletproofs IPA prover (`n = 8`) | `CatCrypt/Crypto/Jasmin/BulletproofsIPAReflect.lean` | `ipaProverBody8_computes`: for every codec with decode ∘ encode the identity, scalar action and challenge function `H`, the `LowCT` body run under `semScalarL` at the leaf oracle `ipaLeafOracle` leaves the encodings of the commitment, the three `(L, R)` pairs and the final scalar of the spec prover `ipaProve … 3 a g`, for all `a`, `G`. `ipaProverBody8_denote`: the same for the `Com` that `translateDialectControl` produces. `ipaProverBody8_computes_ed25519`: the instance over the edwards25519 group, scalars `ZMod L` acting by `lsmul`, points in the RFC 8032 encoding. | Orchestration as a `LowCT` body over leaves that are Lean definitions; the leaves are external calls in the emitted `.jazz`, and `H` is a parameter. |
| Halo2 IPA prover (`n = 8`) | `CatCrypt/Crypto/Jasmin/Halo2IPAProverReflect.lean` | `halo2IPAProverBody8_computes`: for every challenge function `H` and all `a`, `G`, the body `ipaProverBodyN halo2IpaNames` run under `semScalarL` at `halo2LeafOracle H` leaves the encodings of the spec prover `ipaProve pallasSmul H 3 a g` over the Pallas point group (Mathlib `WeierstrassCurve.Affine.Point` of `y² = x³ + 5` over `ZMod pallasQ`) with scalars `ZMod vestaQ`, points in the `pasta_curves` compressed encoding (`pallasIpaCodec`, round trip proved). `halo2IPAProverBody8_denote`: the same for the emitted `Com`. `pallasSmul_emitted`: the scalar action is what `PastaGroupEmit.emittedSmul` computes on the bits of the scalar. | Orchestration as a `LowCT` body over leaves that are Lean definitions (the generic leaves of `BulletproofsIPAReflect` at Pallas); the leaves are external calls in the emitted `.jazz`, and `H` is a parameter. The a/G-only reduction: no blinding polynomial, no `b`-vector or `U` term, no `W` blinds, Bulletproofs fold convention, stateless challenge (module docstring). |

## Ascent

| Primitive | Modules | Theorems | Provenance |
|---|---|---|---|
| Field and word kernels | `SC/Ascent/` ([ASCENT.md](ASCENT.md)); `scripts/ascent-corpus.sh` | `feSub_endToEnd`, `feAdd_endToEnd`, `demo_source_to_bytes`: closed capstones from a `LowCT` kernel to its `Com jasminDialect` denotation. `bash scripts/ascent-corpus.sh` lists the kernels, the kernels with an ascent correspondence, and the kernels reached by a closed capstone. | `LowCT` terms written in Lean, with a front-translated `Com jasminDialect`. |
| Transcribed Ed25519 blocks printed by the project's backend | `SC/Ascent/Demos/Ed25519PointAddBytes.lean`, `Ed25519ScReduceShippedProof.lean`, `Ed25519ScMuladdShippedProof.lean` (same directory) | `paShippedBytes_correct`: the bytes that the package's encoder writes for the transcribed `ed25519_point_add` block decode to a block that computes the extended-coordinate addition formula. `scReduceShipped_correct_addr`: `ed25519_sc_reduce` computes `x mod L`. `scMuladdShipped_correct_addr`: `ed25519_sc_muladd` computes `(a·b + c) mod L`. Each assumes disjoint cells (`Separated`). | Lean transcriptions of the backend's x86-64 text, proved at the address machine `runBlockA`; the bytes are the encoder's, not the assembler's. |

## Kernels at the bytes through the region back half

| Primitive | Modules | Theorems | Provenance |
|---|---|---|---|
| Montgomery field multiply, square, addition, subtraction at P-256, secp256k1, P-384, BN254, BLS12-381 | `SC/Algebraic/FieldLimbs/`; `SC/Haxc/FieldRoute.lean`; `SC/Haxc/FieldInstances.lean`; `SC/Haxc/FieldBlocksCT.lean` | `field_correct_bytes`: for every field record and every result of `compileRegion` on the multiply program, the decoded bytes halt in a state from which the layout reads back the Montgomery limbs of `x * y`. `<prime>_<op>_correct_bytes`: the same statement for each operation at each of the five primes. `nfChainF_ct_<prime>`: constant time of the field chain. | Template over a modulus record, lowered to limbs; [FIAT_TEMPLATES.md](FIAT_TEMPLATES.md). |
| `mpn_add_n`, `mpn_sub_n`, `mpn_mul_1`, `mpn_addmul_1` | `SC/Haxc/MpnBytes.lean` | `mpn_add_n_bytes_correct`, `mpn_sub_n_bytes_correct`, `mpn_mul_1_bytes_correct`, `mpn_addmul_1_bytes_correct`: at every limb count `n`, the decoded bytes of a result of `compileRegion` read back the `n + 1` result words. | Route program through the region back half. |

[bench/PROVENANCE.md](bench/PROVENANCE.md) lists the emitted artifacts this package
ships. The `compileFromHax` modules compile hax `ImpExpr` sources written in the
module; the simulations from hax source to LowCT (`haxToLowCT_simulates_programT`,
`haxToLowCT_simulates_programL`) end at `RustExec`. The pairing and group kernels take
the leaf semantics `leafSem` as a parameter and denote through
`jasminDenoteWith leafSem`. The hax compiler `compileA`, which compiles a hax module
to x86-64 bytes with value, constant-time and robust-compilation theorems, is described
in [PIPELINE.md](PIPELINE.md).
