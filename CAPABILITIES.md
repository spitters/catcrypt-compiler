# Primitive coverage index

This table maps each cryptographic primitive shipped in `catcrypt-compiler` to
(1) the Lean **module** that emits/compiles its bytes, (2) the **emit or
correctness theorem / KAT** that pins that emit, and (3) its **compiler-provenance
class** — how the shipped bytes are justified at the leaf boundary. The provenance
classes are:

- **Lean-descent (front-sourced)** — bytes generated from a Lean spec through the
  verified front (`LowCT → CryptoSSA → Com → jasmin`) and tied to the spec by a
  `Com`-denotation theorem;
- **owned-arithmetic-leaf (runBlock-proven)** — an owned x86 arithmetic leaf
  justified by a `runBlock` denotation proof;
- **trusted-symmetric-leaf (extCall)** — a symmetric permutation/compression left
  as an opaque, trusted `extCall`/called leaf at the boundary;
- **Rust/hax** — bytes sourced from Rust through the hax front;
- **hand-authored (backlog)** — hand-built emit still listed in a provenance
  baseline (`scripts/emit_provenance_baseline.txt`,
  `scripts/handcom-provenance-baseline.txt`) awaiting re-sourcing through a front.

Several primitives carry two stories (fully-proven round arithmetic plus a deployed
owned `.s` whose hot instruction is a trusted leaf); those cells name both. Line
citations are given for the symmetric and pairing rows for spot-checking. Paths are
relative to the repo root.

## Symmetric family

| Primitive | Module | Theorem / KAT | Provenance |
|---|---|---|---|
| AES-128 | `CatCrypt/Crypto/SecureCompilation/VIR/AesRoundCatCryptEmit.lean` (round GF(2⁸) math); `CatCrypt/Crypto/SecureCompilation/X86Backend/Aes128CtrVsimdEmit.lean` (whole CTR `.s`) | `xtimeW_eq_spec` / `mul3W_eq_spec` (`AesRoundCatCryptEmit.lean:92`, `:98`); `ecbCom_denote` (`Aes128CtrVsimdEmit.lean:271`); `asm_has_export` native_decide asm KAT (`:485`) + `#guard` byte checks (`:489`–`:518`) | Round GF(2⁸) arith: **Lean-descent (front-sourced)**, `Com`-denote proven. Deployed CTR keystream: owned whole-`.s` emit whose AES round is the AES-NI `VAESENC` hardware instruction — a **trusted-symmetric-leaf** at the instruction boundary, corroborated by asm KATs. |
| GF(2¹²⁸) / GHASH | `CatCrypt/Crypto/SecureCompilation/VIR/GhashGf128CatCryptEmit.lean` (also owned `VIR/VPClmulEmit.lean`) | `accStepCom_denote` (`GhashGf128CatCryptEmit.lean:259`) and `valStepCom_denote` (`:267`) denote to `GF128.gf128_step`; `accStepW_eq_spec` (`:109`) | **Lean-descent (front-sourced)** — `Com` built on `catCryptDialect` and denote-proven to the `GF128` bit-serial spec. |
| HMAC | `CatCrypt/Crypto/SecureCompilation/VIR/HmacHkdfEmit.lean` | `xorPadCom_denote` (`:278`), `xorPadCom_bindings` (`:255`), `hmacXorPad_has_export` native_decide ABI KAT (`:411`); HKDF-Expand recurrence `expandLoop_denote_eq` (`:390`) | Mixed. The ipad/opad and SHA-2 core are **Lean-descent (front-sourced)** (`FrontSourced`, rfl-provenance, `:626`); the HKDF-Expand step is encapsulated as a single `hkdf_expand_step` **trusted-symmetric-leaf (extCall)** (`:366`–`:390`). |
| Keccak / SHAKE | `CatCrypt/Crypto/SecureCompilation/VIR/KeccakRoundCatCryptEmit.lean` (round); `CatCrypt/Crypto/SecureCompilation/VIR/Shake256SpongeOwnedEmit.lean` (variable-length sponge) | `keccakRound_catcrypt_eq` (`KeccakRoundCatCryptEmit.lean:334`); `shake256Body_front_sourced` (`Shake256SpongeOwnedEmit.lean:350`), `shake256_shape` / `shake256_renders_sponge` native_decide KATs (`:316`, `:357`) | Round permutation arith: **Lean-descent (front-sourced)**, `Com`-denote proven. Deployed SHAKE256: front-sourced sponge marshalling around a **trusted-symmetric-leaf** — the called `keccak_f1600_resident` permutation (FIPS-202 KAT'd). |
| Poly1305 | `CatCrypt/Crypto/SecureCompilation/VIR/Poly1305OwnedCom.lean` (front-compiled owned kernel); also `VIR/ChaChaPolyEmit.lean`, `X86Backend/Poly1305Kernel.lean` (HACL variant) | `poly1305_is_purearith_only` (`Poly1305OwnedCom.lean:254`), `poly1305MacLowered_isSome` native_decide (`:214`); `poly1305_mac_dot` / `poly1305_isPoly` (`ChaChaPolyEmit.lean:156`, `:147`) + jazz `#guard` KATs (`:325`–`:344`) | **Lean-descent (front-sourced)** — 5×26-limb field MAC compiled through the front, no hand-built `Com`; proven pure-arith (no `extCall`). |
| SHA-256 | `CatCrypt/Crypto/SecureCompilation/VIR/Sha256CompressCatCryptEmit.lean` (whole 64-round); round funcs in `VIR/Sha256RoundCatCryptEmit.lean` | `sha256Compress_catcrypt_denote` (`Sha256CompressCatCryptEmit.lean:317`); round-func denote `sha256_smallsigma0_catcrypt_denote` (`:123`) | **Lean-descent (front-sourced)** — `Com`-denote proven equal to the FIPS 180-4 §6.2 reference compression. |
| SHA-512 | `CatCrypt/Crypto/SecureCompilation/VIR/Sha512CompressCatCryptEmit.lean` (whole 80-round); round funcs in `VIR/Sha512RoundCatCryptEmit.lean` | `sha512Compress_catcrypt_denote` (`Sha512CompressCatCryptEmit.lean:317`), `sha512RoundCat_eq` (`:205`), `runRoundsCat_eq` (`:280`) | **Lean-descent (front-sourced)** — `Com`-denote proven equal to the FIPS 180-4 §6.2 reference compression. |
| BLAKE3 | `CatCrypt/Crypto/BLAKE3/CompressEmit.lean`, `CatCrypt/Crypto/BLAKE3/CompressOwnedEmit.lean` | `blake3_lower_denote` (`CompressEmit.lean:257`); `blake3_G_computes_spec` native_decide (`:199`); `blake3_G_lower_denote` (`:189`) | **hand-authored (backlog)** — both files are listed in `scripts/emit_provenance_baseline.txt` as grandfathered hand-authored `List (JInstr)` emission; corroborated by a `runBlock`-proven denotation tie. |

## Field / EC / pairing family

| Primitive | Module | Theorem / KAT | Provenance |
|---|---|---|---|
| BN254 pairing arithmetic | `CatCrypt/Crypto/Pairing/BN254GroupEmit.lean` | `lamCom_denote` (`:324`), `lamComShadow_denote` (`:299`), `lamCom_isSome` (`:280`), `lamCom_eq_shadow` (`:294`), leaf bridge `binLeafExpr_denote` (`:218`) | G1 group-law orchestration **Lean-descent (front-sourced)** via `buildOrchCom` (`:283`–`:324`), over opaque `fp_*` field **`extCall` leaves that are `runBlock`-verified owned-arithmetic** (`:100`). |
| BLS12-377 pairing arithmetic | `CatCrypt/Crypto/Pairing/Bls12_377Emit.lean` | `fieldMulCom_eq_shadow` (`:335`), `fieldAddCom_isSome` (`:275`), `fieldAddCom_eq_shadow` (`:286`), leaf builders at `:224`–`:243` | Field + pairing orchestration **Lean-descent (front-sourced)** via `buildOrchCom` (`:249`), over single-leaf straight-line `extCall`-over-`stackArr` field kernels (**owned-arithmetic-leaf**); corroborated by a **Rust KAT** cross-check `bench/bls12_377_compare/bls377_kat.rs`. |

## Lattice / PQ family

| Primitive | Module | Theorem / KAT | Provenance |
|---|---|---|---|
| HAWK negacyclic multiply | `CatCrypt/Crypto/SecureCompilation/VIR/HawkMulEmit.lean` (HAWK-512 NTT hot phase in `X86Backend/HawkNttOwnedEmit.lean`, `X86Backend/HawkPointwiseOwnedEmit.lean`) | `hawk_denote_spec` native_decide, `hawk_is_purearith_only`, `hawkLowered_isSome` native_decide | **Lean-descent (front-sourced)** — negacyclic ring multiply over `Z/1024[x]/(xⁿ+1)` compiled through the front; proven pure-arith (no `extCall`). |
| NTRU-HRSS ring multiply | `CatCrypt/Crypto/SecureCompilation/VIR/Ntruhrss701MulEmit.lean` (Karatsuba sibling `VIR/Ntruhrss701KaratsubaEmit.lean`) | `ntru_denote_spec` native_decide, `ntru_is_purearith_only`, `ntruLowered_isSome` native_decide | **Lean-descent (front-sourced)** — `Z/8192[x]/(xⁿ−1)` cyclic product through the front, no hand-built `Com`. |
| FN-DSA (Falcon) emit | `CatCrypt/Crypto/SecureCompilation/VIR/FndsaEmit.lean` (reflect surface `Jasmin/FalconReflect.lean`) | `fndsa_emit_verify_denotation_preserves`, `fndsa_emit_sampler_range_preserves`, `fndsa_emit_sampler_ct` (constant-time), `fndsa_emit_sampler_distance_bound`; jazz `#guard` KATs (`:240`+) | **Lean-descent (front-sourced)** — emit carries denotation-preservation, sampler range, and constant-time proofs; corroborated by Jasmin-source `#guard` KATs. |

## Proof-systems family

| Primitive | Module | Theorem / KAT | Provenance |
|---|---|---|---|
| Plonky3 reflect | `CatCrypt/Crypto/Jasmin/Plonky3Reflect.lean` (Merkle) plus the `Jasmin/Plonky3{Air,Fri,Lde,Prove}Reflect.lean` family | Pinned by reflection-reification `#eval` well-formedness checks (`:315`–`:321`); emit routes through the verified chain `LowCT → CryptoSSA → Com → jasmin` | **Lean-descent (front-sourced)** reflect surface. Caveat: several Plonky3 *owned-emit* modules — `VIR/Plonky3OrchLoopsOwnedEmit.lean`, `VIR/Plonky3PaddingFreeSpongeOwnedEmit.lean`, `VIR/Plonky3SerializeOwnedEmit.lean` — are **hand-authored (backlog)** per `scripts/handcom-provenance-baseline.txt`. |
| Bulletproofs reflect | `CatCrypt/Crypto/Jasmin/BulletproofsIPAReflect.lean` | Pinned by reflection-reification `#eval` checks (`:222`–`:223`); reuses already-emitted MSM leaves with realization tie `Pairing/MsmReduce.msm_eq_scalarFold` | **Lean-descent (front-sourced)** reflect surface — IPA reduction orchestration reflected through the verified chain over the already-emitted toy-EC MSM primitive. |

## Notes

- **Rust/hax** provenance is present in the wider GF-MQ emit family
  (`CatCrypt/Crypto/MAYO/KernelFromRustcmdFrontEmit.lean`), but none of the headline
  primitives in `README.md` is Rust/hax-sourced; BLS12-377 uses Rust only as a
  corroborating KAT, not as the byte source.
- Cells reading "pinned by `#eval` reification checks" (Plonky3/Bulletproofs
  reflect) reflect what is present: these surfaces are validated by `#eval`
  reification over the reflected front output rather than a single named `theorem`.
  The correctness obligation lives on the shared front chain; the per-module pin is
  a reification check, not a KAT byte-equality.
- Where a primitive has both a fully-proven round/step kernel and a deployed owned
  `.s` whose hot instruction (`VAESENC`) or called routine (`keccak_f1600_resident`)
  is a trusted leaf, both modules and both classes are named — a two-part provenance.
