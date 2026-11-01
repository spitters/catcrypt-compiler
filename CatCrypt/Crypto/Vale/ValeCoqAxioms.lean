/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# Adopted-leaf constant-time citation index

Citation table for the `_CT` statements of `CatCrypt/Crypto/Vale/`. Each names a
leaf's leakage function (`<leaf>_leak`, in the `LeafLeak` alphabet of
`Vale/LeafLeakage.lean`) and states `SecretIndependent` of it: the leaf's
observable trace does not vary with the argument the row calls secret. Every
row is a proposition (`def … : Prop`) that a theorem about the leaf takes as a
hypothesis. The upstream result that each cites is recorded here with its file and
line.

Parallel to `P256FieldMulCoqAxioms.lean` and the other per-leaf value tables in
this directory, which cover the `_denote` constants. This file covers the
leakage statements only.

## Main definitions

This module declares nothing. It is the citation index for the `_CT` statements
declared in the sibling `Vale/*.lean` modules; the statements themselves, and the
`SecretIndependent` predicate they are stated against, live in those files and in
`Vale/LeafLeakage.lean`. Read a row here to find what upstream result a given
`_CT` statement rests on and how far that result was checked.

## Status legend

| Status | Meaning |
|---|---|
| future | a machine-checked leakage analysis is run on this leaf during the upstream build; the analysis's soundness is proved, but its per-leaf result is not a checked-in theorem |
| cited | the citation is to a typing discipline, a structural property of the code, or an audit claim — not to a machine-checked leakage theorem |
| refuted | the upstream source shows the leaf is variable-time; the row records the reject side |

No row is proved. **No adopted leaf in this directory has a checked-in,
per-leaf, machine-checked constant-time theorem upstream.** The two mechanisms
that come closest are Vale's build-time taint analysis (status future) and HACL\*'s
`Lib.IntTypes` secret-integer typing (status cited); the AUCurves and fiat-crypto sides
have neither, and rest on fixed public iteration counts and branch-free
generated code.

## Upstream repositories these paths refer to

| Prefix | Repository |
|---|---|
| `hacl-star/` | https://github.com/hacl-star/hacl-star |
| `AUCurves/` | https://github.com/AU-COBRA/AUCurves |
| `fiat-crypto/` | https://github.com/mit-plv/fiat-crypto (a submodule of AUCurves) |
| `libjade/` | https://github.com/formosa-crypto/libjade |

## The two upstream mechanisms

**Vale x64 taint analysis.** The checker and its soundness lemma are
machine-checked: `hacl-star/vale/specs/hardware/Vale.X64.Leakage_s.fst`:101
(`isLeakageFree`), :76 (`isConstantTime`); `hacl-star/vale/code/arch/x64/Vale.X64.Leakage.fst`:433
(`val lemma_code_leakage_free`), :440 (`check_if_code_is_leakage_free'`). The
checker is invoked once, over the whole procedure list, at
`hacl-star/vale/code/lib/util/CmdLineParser.ml`:71, failing the build at :72.

Two caveats keep every Vale row at future rather than proved. The exported
signature actually called is the unrefined
`hacl-star/vale/code/arch/x64/Vale.X64.Leakage.fsti`:9 (`: bool`); the
refinement-carrying `check_if_code_is_leakage_free'` has no call site. And no
per-procedure leakage lemma is checked into the tree — a search for
`va_lemma_*_leakage` finds none. The guarantee is "the build ran a verified
analysis and it returned true", not "here is the theorem".

**HACL\* secret-integer typing.** `hacl-star/lib/Lib.IntTypes.fsti`:137
(`val sec_int_t: inttype -> Type0`, abstract), :173 (`type uint8 = uint_t U8 SEC`),
:191 (`type uint64 = uint_t U64 SEC`). Values of these types cannot be branched
on or used as indices, so a well-typed body is secret-independent by
construction. No leakage theorem exists: a search for `leakage` /
`isConstantTime` over `hacl-star/code/` and `hacl-star/lib/` finds nothing.
The project scopes the claim itself at
https://github.com/hacl-star/hacl-star/blob/main/SECURITY.md (line 6) — "HACL\* only
protects against remote timing attacks and so it is possible that there are
side-channel leaks in the compiled code."

## Vale-verified assembly

| Lean declaration | Status | Citation |
|---|---|---|
| `AESGCM.Vale_AES128_GCM_encrypt_CT` | future | `hacl-star/vale/code/crypto/aes/x64/Main.ml`:10 registers `gcm128_encrypt_opt` into the list the analysis at `CmdLineParser.ml`:71 checks. Source procedure `hacl-star/vale/code/crypto/aes/x64/Vale.AES.X64.GCMencryptOpt.vaf`:1562 (`procedure Gcm_blocks_stdcall`); `Secret` taint on the key and plaintext buffers at `hacl-star/vale/code/arch/x64/interop/Vale.Stdcalls.X64.GCMencryptOpt.fst`:37. Emitted symbol `hacl-star/dist/vale/aesgcm-x86_64-linux.S`:2889. |
| `GHASH.Vale_aes128_keyhash_init_CT` | future | `hacl-star/vale/code/crypto/aes/x64/Main.ml`:4 registers `aes128_keyhash_init`. Source procedure `hacl-star/vale/code/crypto/aes/x64/Vale.AES.X64.GF128_Init.vaf`:219, with `Secret` taint preconditions at :243 and :244; interop taint at `hacl-star/vale/code/arch/x64/interop/Vale.Stdcalls.X64.AesHash.fst`:34. Emitted symbol `hacl-star/dist/vale/aesgcm-x86_64-linux.S`:112. |
| `Curve25519.Vale_Hacl_Curve25519_64_CT` | future | Extern-assembly build only: `hacl-star/vale/code/crypto/ecc/curve25519/Main25519.ml`:17 (`fmul_e`), :19 (`fsqr_e`), :23 (`cswap2_e`); sources `hacl-star/vale/code/thirdPartyPorts/rfc7748/curve25519/x64/Vale.Curve25519.X64.FastWide.vaf`:138 and :561, `…FastUtil.vaf`:974; `Secret` taint at `hacl-star/vale/code/arch/x64/interop/Vale.Stdcalls.X64.Fmul.fsti`:38. **The inline-assembly build is not checked**: `hacl-star/vale/code/crypto/ecc/curve25519/Inline25519.ml`:9 calls the printers directly with no `parse_cmdline` invocation, and `hacl-star/dist/gcc-compatible/Hacl_Curve25519_64.c`:63 selects between the two on `HACL_CAN_COMPILE_INLINE_ASM`. The inline path rests on the same `Secret` taint in `hacl-star/vale/code/arch/x64/interop/Vale.Inline.X64.Fmul_inline.fst`:37, verified against the Vale spec but not re-run through the analyser. |

## HACL\* F\*-verified C

| Lean declaration | Status | Citation |
|---|---|---|
| `ChaCha20Vec256.Vale_Hacl_Chacha20_Vec256_CT` | cited | Typing discipline. `hacl-star/code/chacha20/Hacl.Chacha20.Vec256.fst`:15; signature carrying the secret types at `hacl-star/code/chacha20/Hacl.Impl.Chacha20.Vec.fst`:220-224, `val` at :235. Emitted symbol `hacl-star/dist/gcc-compatible/Hacl_Chacha20_Vec256.h`:39. No leakage theorem in `code/chacha20/`. |
| `SHA256.Vale_Hacl_Hash_SHA2_sha256_update_nblocks_CT` | cited | Typing discipline for the C leaf we link. Declaration `hacl-star/dist/gcc-compatible/internal/Hacl_Hash_SHA2.h`:116; F\* source `hacl-star/code/sha2-mb/Hacl.SHA2.Scalar32.fst`:23; secret-typed signature `hacl-star/code/sha2-mb/Hacl.Impl.SHA2.Generic.fst`:296. A Vale SHA-256 exists and *is* leakage-checked (`hacl-star/vale/code/crypto/sha/ShaMain.ml`:3, source `hacl-star/vale/code/thirdPartyPorts/OpenSSL/sha/Vale.SHA.X64.vaf`:737, symbol `hacl-star/dist/vale/sha256-x86_64-linux.S`:2), but it is a different symbol from the one this leaf binds. |
| `SHA512.Vale_Hacl_Hash_SHA2_sha512_update_nblocks_CT` | cited | Typing discipline. Declaration `hacl-star/dist/gcc-compatible/internal/Hacl_Hash_SHA2.h`:134; F\* source `hacl-star/code/sha2-mb/Hacl.SHA2.Scalar32.fst`:62; same secret-typed signature at `hacl-star/code/sha2-mb/Hacl.Impl.SHA2.Generic.fst`:296. There is no Vale SHA-512: `hacl-star/vale/code/crypto/sha/ShaMain.ml` registers only `sha256_update`. |
| `Ed25519.Vale_Hacl_Ed25519_sign_CT` | cited | Typing discipline. `hacl-star/code/ed25519/Hacl.Ed25519.fsti`:86-90 (`val sign`, all buffers `uint8` = `SEC`), body at `hacl-star/code/ed25519/Hacl.Ed25519.fst`:52, driver `hacl-star/code/ed25519/Hacl.Impl.Ed25519.Sign.fst`:55. The signing path takes no declassification. |
| `Ed25519.Vale_Hacl_Ed25519_verify_not_CT` | refuted | The verify path declassifies and branches. `hacl-star/code/ed25519/Hacl.Impl.Ed25519.PointEqual.fst`:40-41 opens `Lib.RawIntTypes` and branches on `u64_to_UInt64 s4 >^ 0x00000010000000uL` (the `s < q` scalar range check), reached from `hacl-star/code/ed25519/Hacl.Impl.Ed25519.Verify.fst`:58; the point-equality test at `…PointEqual.fst`:207-213 is a short-circuiting `&&` chain over declassified limbs, reached from `…Verify.fst`:38. The signature returns a public `bool` (`hacl-star/code/ed25519/Hacl.Ed25519.fsti`:112). |

## libcrux ML-KEM-768

| Lean declaration | Status | Citation |
|---|---|---|
| `MLKEM768.Vale_libcrux_mlkem768_keygen_CT` | cited | **No upstream checkout available.** libcrux is not among the local repositories, so nothing was located and nothing is cited. The claim rests on libcrux's secret-independence audit as described in its own documentation, unverified here. |
| `MLKEM768.Vale_libcrux_mlkem768_encaps_CT` | cited | As above. |
| `MLKEM768.Vale_libcrux_mlkem768_decaps_CT` | cited | As above. |

## AUCurves Bernstein–Yang safegcd inversion

The shared structural fact for every row below: the divstep iteration count is
a closed function of the modulus bit-length, computed at synthesis time, and
the loop is a bounded `N.iter`. The formula is
`fiat-crypto/src/PushButtonSynthesis/WordByWordMontgomery.v`:121 —
`if bits <? 46 then (49 * bits + 80) / 17 else (49 * bits + 57) / 17`, with the
generic reference implementation at
`fiat-crypto/src/Arithmetic/BYInv_fullproof_ref/Ref.v`:68 and its bounded
iteration at :88. The convergence framework is
`AUCurves/src/Arithmetic/safegcd/divsteps_theory.v`:799
(`Theorem processDivstep_correct`), with the inverse corollary at :909.

Two facts keep every row at cited. The count being public is a structural
property, not a stated theorem — nothing in AUCurves or fiat-crypto states a
leakage or noninterference result about these leaves. And only the Curve25519
convergence certificate is `Qed`-closed
(`AUCurves/src/Arithmetic/safegcd/divsteps590.v`:36-41); every other per-curve
certificate is an `Axiom` with an OCaml re-check driver beside it.

| Lean declaration | Status | Citation |
|---|---|---|
| `SafegcdCurve25519.Vale_safegcd25519_fe25519_inv_CT` | cited | Certificate `AUCurves/src/Arithmetic/safegcd/divsteps590.v`:36 (`Lemma p25519_certificate_590`, `Qed` at :41), count at :43 (590). Inversion instantiation `AUCurves/src/Bedrock/Field/Synthesis/Examples/Fe25519_FpInv.v`:83, top theorem at :446. |
| `SafegcdBLS12_381.Safegcd_BLS12_381_invert_CT` | cited | Certificate `AUCurves/src/Arithmetic/safegcd/divsteps_bls12.v`:20 (`Axiom bls12_certificate`), count at :23 (1078). Instantiation `AUCurves/src/Bedrock/Field/Synthesis/Examples/BLS12_FpInv.v`:77-80. |
| `SafegcdSecp256k1.AUCurves_safegcd_secp256k1_invert_CT` | cited | Certificate `AUCurves/src/Arithmetic/safegcd/divsteps_secp256k1.v`:30, count at :33 (741). Instantiation `AUCurves/src/Bedrock/Field/Synthesis/Examples/Secp256k1_FpInv.v`:62-65. |
| `SafegcdP256.AUCurves_safegcd_p256_invert_CT` | cited | Certificate `AUCurves/src/Arithmetic/safegcd/divsteps_p256.v`:30, count at :33 (741). Instantiation `AUCurves/src/Bedrock/Field/Synthesis/Examples/P256_FpInv.v`:63. |
| `SafegcdP384.AUCurves_safegcd_p384_invert_CT` | cited | Certificate `AUCurves/src/Arithmetic/safegcd/divsteps_p384.v`:29, count at :32 (1110). Instantiation `AUCurves/src/Bedrock/Field/Synthesis/Examples/P384_FpInv.v`:58-61. |
| `SafegcdP521.AUCurves_safegcd_p521_invert_CT` | cited | Certificate `AUCurves/src/Arithmetic/safegcd/divsteps_p521.v`:30, count at :33 (1505). Instantiation `AUCurves/src/Bedrock/Field/Synthesis/Examples/P521_FpInv.v`:59. |
| `SafegcdBN254.AUCurves_safegcd_bn254_invert_CT` | cited | Certificate `AUCurves/src/Arithmetic/safegcd/divsteps_bn254.v`:30 (`Axiom bn254_certificate`), count at :33 (735). Instantiation `AUCurves/src/Bedrock/Field/Synthesis/Examples/BN254_FpInv.v`:67, with the iteration formula re-derived at :67-70 from the modulus bit-length at :53. |
| `Pallas.Safegcd_Pallas_invert_CT` | cited | Certificate `AUCurves/src/Arithmetic/safegcd/divsteps_pallas.v`:29, count at :32 (738). Instantiation `AUCurves/src/Bedrock/Field/Synthesis/Examples/Pallas_FpInv.v`:67. |
| `Vesta.Safegcd_Vesta_invert_CT` | cited | Certificate `AUCurves/src/Arithmetic/safegcd/divsteps_vesta.v`:29, count at :32 (738). Instantiation `AUCurves/src/Bedrock/Field/Synthesis/Examples/Vesta_FpInv.v`:67. |
| `MpnInvert.MpnInvert_Safegcd_CT` | cited | The general-modulus form of the same argument: the iteration formula at `fiat-crypto/src/PushButtonSynthesis/WordByWordMontgomery.v`:121 as a function of the modulus, and the bounded loop at `fiat-crypto/src/Arithmetic/BYInv_fullproof_ref/Ref.v`:88. The modulus is the public parameter of the proposition, which is what makes the count public. |

## AUCurves pairing base-field arithmetic

| Lean declaration | Status | Citation |
|---|---|---|
| `BN254.Vale_AUCurves_BN254_Fp_CT` | cited | 4×u64 word-by-word Montgomery at `AUCurves/src/Bedrock/Field/Synthesis/Examples/bn254_prime.v`:31, synthesised through `Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery` (imported at :7). The generated code is straight-line: `fiat-crypto/fiat-c/src/p256_64.c` (the same generator at a different prime) has no `if`/`for`/`while` in code, and conditional selection is masked — `fiat-crypto/fiat-c/src/p256_64.c`:152 inside `fiat_p256_cmovznz_u64` at :146, with the compiler barrier at :47. |
| `BN254.Vale_AUCurves_BN254_Fp12_CT` | cited | Tower instances `AUCurves/src/Bedrock/Field/Synthesis/Examples/bn254_instances.v`:46-48, `…/bn254_Fp2.v`; the `Fp12` operation list at `AUCurves/src/Bedrock/Field/Synthesis/Examples/BN254_Pairing.v`:315. A fixed sequence over the Fp leaves above. |
| `BN254.Vale_AUCurves_BN254_pairing_CT` | cited | Fixed loop bound 64: `AUCurves/src/Bedrock/Field/Synthesis/Examples/BN254_Pairing.v`:789-790, function `bn254_miller_loop_optimal` at :1230 with its own bound at :1222-1223. The loop body does branch (`cmd.cond (expr.var "bit")` at :646), on a bit of the **public** curve parameter `|6u + 2|` (:573-577, constant at `AUCurves/src/Bedrock/Field/Synthesis/Examples/BN254_MillerLoop.v`:266) — not on an operand. The correctness lemma at `…/BN254_MillerLoop.v`:484 is functional only. |
| `BN254.Vale_AUCurves_BN254_miller_loop_CT` | cited | Same loop, same bound; measure fixed at 64 in the invariant, `AUCurves/src/Bedrock/Field/Synthesis/Examples/BN254_MillerLoop.v`:285. |
| `BN256.Vale_AUCurves_BN256_Fp_CT` | cited | `AUCurves/src/Bedrock/Field/Synthesis/Examples/bn256_prime.v`:31 (4 limbs). BN256 is a parallel development, not shared files with BN254. |
| `BN256.Vale_AUCurves_BN256_Fp12_CT` | cited | Tower at `AUCurves/src/Bedrock/Field/Synthesis/Examples/bn256_instances.v` / `…/bn256_Fp2.v`; `Fp12` operation list at `AUCurves/src/Bedrock/Field/Synthesis/Examples/BN256_Pairing.v`:298. |
| `BN256.Vale_AUCurves_BN256_pairing_CT` | cited | Fixed loop bound 65: `AUCurves/src/Bedrock/Field/Synthesis/Examples/BN256_Pairing.v`:614-615, function at :620. Functional correctness at `AUCurves/src/Bedrock/Field/Synthesis/Examples/BN256_MillerLoop.v`:586. |
| `BN256.Vale_AUCurves_BN256_miller_loop_CT` | cited | Same loop and bound as the row above. |
| `BLS12_377.AUCurves_bls377_CT` | cited | Field leaves: same fiat-crypto word-by-word Montgomery generator, branch-free as cited in the BN254 Fp row. Inverse: certificate `AUCurves/src/Arithmetic/safegcd/divsteps_bls12_377.v`:29, count at :32 (1090); instantiation `AUCurves/src/Bedrock/Field/Synthesis/Examples/BLS12_377_FpInv.v`:63. |

## No upstream located

| Lean declaration | Status | Citation |
|---|---|---|
| `Secp256k1Ecmult.Secp256k1Ecmult_const_CT` | cited | **Nothing was found.** `ecmult` appears nowhere in AUCurves, libjade or formosa-25519, and no libsecp256k1 source is vendored. AUCurves has secp256k1 field arithmetic and point addition only (`AUCurves/src/Bedrock/Curve/Secp256k1_G1_Add_Spec.v`:136, :666), no scalar multiplication. libsecp256k1 itself is not formally verified; the axiom cites its authors' constant-time design intent, nothing machine-checked. |

## What fiat-crypto does and does not claim

fiat-crypto states no constant-time theorem. The exhaustive search over its
Coq sources for `constant.time` / `noninterference` / `leakage` returns
comments, identifiers and CLI help text only. The development says so itself at
`fiat-crypto/src/Bedrock/P256/Specs.v`:320 — "This ensures conditional safety,
not a proof of constant-time execution." The nearby
`fiat-crypto/src/Bedrock/P256/Jacobian.v`:457
(`Lemma p256_point_add_constant_time_ok`) is named for the precondition it
discharges, not for a leakage property.

Its vendored bedrock2 does carry a leakage program logic
(`fiat-crypto/rupicola/bedrock2/bedrock2/src/bedrock2/LeakageSemantics.v` and
the `bedrock2Examples/ct.v` examples), and AUCurves carries an information-flow
type checker for its Rust command language
(`AUCurves/src/Bedrock/SafeRustEd25519CTLevel.v`:280, `cmd_ct_safe`). Neither is
applied to the curve, pairing or safegcd code, and the checker has no soundness
theorem — `AUCurves/src/Bedrock/SafeRustEd25519CTLevel.v`:283-286 records
noninterference as a paper claim with the operational proof out of scope.

## Adjacent machine-checked results that these rows do not cite

libjade carries EasyCrypt leakage-equivalence proofs — e.g.
`libjade/proof/crypto_scalarmult/curve25519/amd64/ref4/extracted_ct_proof.ec`:3-8,
an `equiv` concluding `={M.leakages}` from equal public inputs — covering
X25519, SHA-256/512, SHA-3, SHAKE, Poly1305, ChaCha20 and Salsa20, and the
Jasmin speculative-constant-time checker runs in its CI
(`libjade/build-common/Makefile.checksct`:17,
`libjade/.github/workflows/amd64-linux.yml`:40-41; likewise
`formosa-25519/src/Makefile.checksct`:14). These prove the same algorithms
constant-time in a different implementation. They are not evidence about the
leaves adopted here, which bind HACL\*, Vale and AUCurves symbols, and no row
above cites them.

## See also

* `CatCrypt/Crypto/Vale/LeafLeakage.lean` — `LeafLeak` and `SecretIndependent`.
* `CatCrypt/Crypto/Jasmin/LowCTCTAnalysis.lean` — `cmdCT` and `LeafCTTable`,
  the program-level analysis whose per-leaf side condition these statements carry.

This file is intentionally declaration-free (markdown only). Every statement
named above is declared in the module its row's prefix names.
-/

@[expose] public section
