# Benchmark record

Every figure below is transcribed from the CatCrypt owned-emit scoreboard at its
revision of 2026-08-11; it is the only source of figures here. That scoreboard was
reconciled on 2026-09-15 against an artifact-tied per-row record in which each row
names the binary it measured and carries a dated note, and the figures below
follow the reconciled scoreboard. Method, as the
scoreboard states it: core-pinned (`taskset`), `lfence;rdtsc`, min-of-N, on one
host — AMD Ryzen 7 PRO 7840U (Zen 4), carrying GFNI, AVX2, AVX-512, SHA-NI, VAES
and VPCLMULQDQ. Each cycle figure is printed only when the row's known-answer
test passes byte-identically against its reference or official vector; a passing
KAT is test evidence, not a correctness proof. A ratio is ours divided by the
reference, below 1.00 our side being faster, and it compares only at the same
hardware instruction tier; the "same-tier" column carries the scoreboard's
reading of each row. "Owned x86 backend" is this package's own lowering and
assembly printer, as distinct from Jasmin's compiler `jasminc`.

No ratio here can be reproduced from this package: the timing harnesses, the
reference builds and the emit-provenance audit are not part of it. The "artifact" column names the file shipped under `bench/` for
the row, or states that none is; [bench/PROVENANCE.md](bench/PROVENANCE.md)
describes every shipped `.s` file and the declaration that writes it. Per the
audit, the SNOVA, SDitH, MQOM and FrodoKEM benched objects descend from a `LowCT`
term through the verified front; the Poly1305 and scalar SHA-256 objects are
`Com` programs built in Lean and printed by the owned printer; the SHA-NI and
vector SHA-2 and Keccak objects are assembled as text; the QR-UOV path has two
possible writers at different chain depths, with the ratio not saying which was
linked; the NTRU and ChaCha objects carry no audit row.

This page is the timing view of the package's kernels, not the inventory of them.
The inventory is [CAPABILITIES.md](CAPABILITIES.md), the per-primitive index of
modules, theorems and provenance classes; the scoreboard times a small part of
it, and the last section lists the emit targets it does not reach.

## (A) Emitted hot kernels against the fastest production kernel

The verified front emits the inner arithmetic kernel, KAT'd byte-identical to the
reference's own kernel; this is not the whole protocol.

| kernel | reference (tier) | ratio | same-tier | KAT | artifact |
|---|---|---:|---|---|---|
| SNOVA GF(16) multiply, GFNI | SNOVA upstream GFNI ring-dot, `VGF2P8MULB` (GFNI) | 0.85× | survives | 7/7 | none |
| SDitH GF(251) syndrome / RS-eval | sdith-ref Barrett (scalar) | 0.57× | survives | 6/6 | none |
| QR-UOV GF(127) block matvec | QR-UOV Mersenne ref (scalar) | 1.00× | parity | 6/6 | none |
| MQOM GF(251) MQ-eval, N = 8 | mqom-ref `%251` (scalar) | 1.18× | ours slower, same-tier | 6/6 | none |
| NTRU hrss701 ring multiply, 2-way Karatsuba | ntruhrss701 ref, `%`-idiv (scalar) | 1.22× | ours slower, same-tier | 12/12 | none |

Corrections the scoreboard records: the SNOVA, SDitH, QR-UOV and MQOM figures
correct 3.36×, 2.77×, 1.35× and 1.36×, which benched a legacy string-template
scalar emit rather than the front-compiled kernel; SNOVA's 0.85× (range
0.85–0.91×) also corrects a committed 0.82× taken against the SNOVA scalar
multiply table, a GFNI-against-scalar tier mismatch; NTRU's 1.22× corrects
1.35×, measured on a Toom-Cook path that emitted nothing. MQOM's 1.18× is a
serial latency-bound accumulator, where a Barrett leaf measured 594 cycles and
was reverted.

SDitH's 0.57× (132 against 231 cycles) comes from the 2026-07-28 re-measurement
recorded in geomean_ratios.tsv; it corrects the 0.71× (165 against 231) this
page carried before the 2026-09-15 reconciliation, which belonged to a render
whose generator built hand-authored `Linstr`/`Lopn` lists and was retired, and
which the artifact-tied record withdraws rather than re-measures.

Three rows in this table the artifact-tied record disputes without settling, so
they stand as the scoreboard states them. Against SNOVA's own production
constant-time multiply table, that record measures the owned bit-serial GF(16)
twin at 6.55× and the owned GFNI variant at 5.03× on the Tier-2 m = 8 inner loop
(re-measured 2026-08-26), and the ring-dot fold at 1.43× against the reference
opt64 multiply-table fold; the 0.85× above is a different kernel shape, n = 4 and
l = 2, against upstream's own `USE_GFNI` primitive. For MQOM it holds 1.150×
against the same reference, undated, on an artifact absent from disk. For QR-UOV
it holds 1.200×, carried forward rather than re-measured, against an in-tree
schoolbook GF(127) reference rather than the QR-UOV Mersenne one.

## (B) Adopted-validated-leaf rows

A composed primitive over emitted kernels, optionally using a fast leaf proven
byte-identical to the verified owned emit but scheduled by an untrusted compiler.

| primitive | reference (tier) | ratio | same-tier | KAT | artifact |
|---|---|---:|---|---|---|
| ChaCha20-Poly1305, 114 B | HACL\* Simd128 (128-bit SIMD) | 0.99× | parity | RFC 8439 §2.8.2 | none |
| HMAC-SHA256, 8 B, amortised over precomputed pad midstates | HACL\* scalar SHA-2 | 1.06× | ours slower, same-tier | RFC 4231 TC1/2/6 | `hmac_compare/gen/sha256_compress.s`, `hmac_compare/gen/hmac_xor_pad.s` ship; the package does not record them as the timed objects |
| HKDF-SHA256, L = 512 | HACL\* scalar SHA-2 | 1.25× | ours slower, same-tier | RFC 5869 TC1 | none |

At the smaller sizes the scoreboard records HMAC 1.18× at 64 B and HKDF 1.73× at
L = 64. The ChaCha20-Poly1305 row corrects a committed 0.82–0.93×, which linked
HACL\*'s scalar AEAD under a "Vec256" label and a spill-heavy 4-way ChaCha rather
than the XMM-resident variant; against HACL\* Simd256 (AVX2, a higher tier) the
same measurement is 0.92–0.94×. The HMAC and HKDF rows correct a composed form
that re-padded per message and showed a 2.0× tax, which the one-shot path retains.

All three rows are disputed in the artifact-tied record without being settled.
For ChaCha20-Poly1305 it carries 1.660× at long-message cycles per byte against
HACL\* `Chacha20Poly1305_encrypt`, a different size regime, and 2.515× at the same
114 B against libcrux's hacl-rs rather than HACL\* Simd128 and on the spill-heavy
4-way render this row's correction replaced. For HMAC it carries 1.220× at 64 B
and for HKDF 2.050× at L = 64 and 1.38× at L = 512, both re-measured 2026-07-27
through the same harnesses but timing the native-`ror` compression core rather
than the resident one these rows time; neither date is established as later than
the scoreboard's.

## (C) Whole-protocol owned rows

The whole protocol API assembled with every arithmetic kernel emitted by the
verified front; only non-cryptographic control plumbing is adopted reference.

| protocol | reference (tier) | ratio | same-tier | KAT | artifact |
|---|---|---:|---|---|---|
| FAEST-128s sign, gcc-O3 Keccak leaf | faest-ref v2.0.4 (scalar) | 2.1× | ours slower, same-tier | 4506-byte signature byte-identical | none |
| FAEST-128s sign, owned-max 8-way Keccak | faest-ref v2.0.4 (scalar) | 2.68× | ours slower, same-tier | 4506-byte signature byte-identical | none |
| SLH-DSA-SHA2-128s sign, SHA-NI owned leaf | liboqs `slh_dsa_pure_sha2_128s` (scalar SHA-2) | 0.556× | tier mismatch | 7856-byte signature byte-identical to NIST ACVP tcId=157 | none |
| SLH-DSA-SHA2-128s sign, scalar owned leaf | liboqs (scalar SHA-2) | 6.87× | ours slower, same-tier | byte-identical | none |
| FrodoKEM-640-SHAKE encaps | liboqs `frodokem_640_shake` (AVX2) | 28× | ours slower; scalar against AVX2, not a same-tier comparison | ciphertext (9752 B) and shared secret (16 B) byte-identical | none |

The SLH-DSA 0.556× is our SHA-NI leaf against a portable scalar C SHA-256, and no
SHA-NI SLH-DSA reference exists on this host, so the same-tier figure is the 6.87×
scalar row. FAEST's 2.1× uses a gcc-O3 Keccak leaf proven byte-identical to the
verified owned emit over the XKCP zero state and 200000 random states; the
gcc-free path is the 2.68× row. FrodoKEM's 28× the scoreboard attributes to a
by-value-leaf ABI cost, not to arithmetic.

The FAEST rows are disputed in the artifact-tied record, which times the same
owned-max harness at 95.6M cycles against a faest-ref v2.0.4 rebuilt with AVX2
Keccak and AES-NI at 85.2M, for 1.120×. Two things differ from the rows above at
once: the reference here is the shipped scalar build, and our side has moved,
because the record's 95.6M postdates a resident-Keccak leaf landing on the seed
tree while the 2.68× carries 189M from before it. The reference builds sit at
different instruction tiers, so 1.120× replaces neither figure. The record's
nearest FrodoKEM row measures the matmul kernel at 8.790× against HACL\*, not the
whole encapsulation against liboqs.

## Owned x86 backend against `jasminc` on the same emitted programs

Both compilers consume the identical emitted `Com`; only the register allocator
differs.

| aggregate | value |
|---|---:|
| geomean owned / `jasminc`, 9 both-emit kernels | 0.7490× |
| geomean owned / s2n-bignum production, 8 covered kernels | 0.5785× |

The 9-kernel 0.7490× (owned about 1.34× faster) is the scoreboard's headline. A
re-measurement over 11 both-emit kernels records 0.575×: the set grew by
`pasta_field_add` and `pasta_field_sub`, where `jasminc` allocates anomalously
badly (owned about 7 cycles against 33–36, ratios 0.19× and 0.22×), and those two
dominate that geomean, so it is recorded and not taken as the headline. The
commit-time run of the same harness gave 0.7249× and 0.5211× against the
committed re-run's 0.7490× and 0.5785×, which the scoreboard reads as 1.34–1.38×
rather than as a precise figure. The s2n-bignum aggregate carries the caveat that
s2n's add and sub are generic-looped against an unrolled fixed-n emit. `jasminc`
rejects, with a no-free-register allocation abort, 6 kernels the owned spilling
allocator emits: the unrolled mpn add and sub at n ≥ 16, and sqr_basecase.

## gcc-oracle headroom map

gcc-O3 is untrusted and KAT-pinned byte-identical to the verified emit on the
official vector and a large random batch; the scoreboard uses it to quantify
recoverable headroom, not as our side of a comparison.

| kernel | verified emit (cyc) | gcc-oracle (cyc) | recoverable | note |
|---|---:|---:|---:|---|
| SHA-256 compression | 3434 | 517 | 6.65× | the gcc leaf is 1.06× ahead of HACL\* |
| SHA-512 compression | 5479 | 634 | 8.64× | the gcc leaf is 1.27× ahead of HACL\* |
| Poseidon2-BabyBear, width 16 | 102739 | 5999 | 17.13× | the gcc leaf is 2.96× ahead of -O2 C |
| fe25519 multiply, 4×64 with reduction | 40.3 | 68.1 | 0.59× | no headroom: at MULX/s2n parity, gcc loses |

Recovery tracks register pressure. The scoreboard records the verified Com→Com
optimizer as inert on register-resident bodies: routed forward with mem2reg and
spill on X25519 it measures 1.785–1.818× against the monolithic emit's 1.714×,
the Keccak scheduler measures 1.01× and CSE 1.04×.

## Shipped artifacts without a timing row

The package tracks ten assembly artifacts; `bench/PROVENANCE.md` lists each with
the declaration that writes it. None carries a row above.

| artifact | status |
|---|---|
| `sha2_linear_compare/sha256_owned_body.s`, `sha2_linear_compare/sha512_owned_body.s` | body-only renders without prologue, epilogue or return; the scoreboard's SHA-2 figures are the gcc-oracle rows above and name no file |
| `keccak_linear_compare/keccak_owned.s` | no scoreboard row for Keccak-f1600; per `bench/PROVENANCE.md` no module writes a file of this name |
| `x25519_fieldmul_compare/gen/fe25519_mul_proven.s` | a different render from the one the fe25519 headroom row times |
| `bn254_fieldmul_compare/gen_com/bn254_mont_mul_x86_from_lean.s` | no scoreboard row for BN254 field multiplication |
| `bls12_377_compare/gen_com/bls12_377_orch_owned.s` | no scoreboard row; the orchestration is emitted by the owned backend, and the field and pairing arithmetic are external calls into the AUCurves bedrock2 routines |

`cryptopt/fiat_curve25519_carry_mul.asm` and
`cryptopt/fiat_curve25519_solinas_square.asm` are not benchmark artifacts; they
are inputs to the ascent proofs ([ASCENT.md](ASCENT.md)).

The other directories under `bench/` are emit targets whose assembly is a build
output rather than a tracked file, and none of them carries a timing row either.
The "module" column names a module that names the emit path; `bench/PROVENANCE.md`
states the writing declaration for the ten tracked artifacts only. The class is
read from that module's own emit markers, in the vocabulary of
[CAPABILITIES.md](CAPABILITIES.md): front-generated when the module invokes a
front stage, builder `Com` when it builds and prints a `Com` or `Lprog` without
one, text when the body is joined from `String` renderers, and driver when the
module holds the `emitMain` and its body comes from its imports. Per-primitive theorem strength is in that file, not here.

| directory | primitive | module | class |
|---|---|---|---|
| aes_xts_compare | AES-XTS tweak | `SC/X86Backend/XtsTweakKernel.lean` | driver |
| chacha_compare | ChaCha20 block, five renders | `SC/VIR/Chacha20BlockEmit.lean` and siblings | builder `Com` |
| keccak_compare | Keccak-f1600, resident and SIMD renders | `SC/VIR/KeccakResidentChiRowEmit.lean`, `SC/VIR/KeccakSimdSingleEmit.lean` | text |
| lea_lsh_compare | LEA round | `SC/X86Backend/LeaRoundThirEmit.lean` | front-generated |
| thir_front_sha256_* (six) | SHA-256 Σ, σ1, message schedule, round, T1, T2 | `SC/X86Backend/Sha256BigSigmaThirEmit.lean` and five siblings | front-generated |
| thir_front_sha512_* (five) | SHA-512 Σ, σ, Ch and Maj, message schedule, T1 | `SC/X86Backend/Sha512BigSigmaThirEmit.lean` and four siblings | front-generated |
| thir_front_sigma0 | SHA-256 σ0 | `SC/X86Backend/Sigma0FrontEmit.lean` | builder `Com` |
| thir_front_blake2b_g_owned | BLAKE2b G function | `SC/X86Backend/Blake2bGThirEmit.lean` | front-generated |
| thir_front_chacha_qr_owned | ChaCha quarter-round | `SC/X86Backend/ChaChaQRThirEmit.lean` | front-generated |
| thir_front_treehash_owned | treehash chain | `SC/X86Backend/TreehashChainEmit.lean` | front-generated |
| wots_chain_owned | WOTS+ chain | `SC/X86Backend/WotsChainEmit.lean` | front-generated |
| thir_front_montmul_owned | BabyBear Montgomery multiply | `SC/X86Backend/MontMulThirEmit.lean` | front-generated |
| thir_front_ntt_bfly_owned | NTT butterfly | `SC/X86Backend/NttBflyThirEmit.lean` | front-generated |
| thir_front_pilot | four-lane dot product | `SC/X86Backend/Dot4FrontEmit.lean` | builder `Com` |
| x25519_compare | X25519 ladder step | `SC/X86Backend/X25519LadderStepBundle.lean` | builder `Com` |
| x25519_ladder_compare | X25519 monolithic ladder step | `SC/X86Backend/X25519MonoLadderKernel.lean` | builder `Com` |
| x25519_fieldmul_compare | Curve25519 field multiply, optimized render | `SC/X86Backend/Fe25519MulOptimized.lean` | builder `Com` |
| secp256k1_compare | secp256k1 Montgomery multiply, 128-bit widening multiply | `SC/X86Backend/Secp256k1MontMulKernel.lean`, `SC/FieldWidenMulEmitCurve.lean` | builder `Com` |
| bytes_direct_secp256k1_femul_runblock | secp256k1 field multiply run through `runBlock` | `SC/X86Backend/EcFeMulReduceComplete.lean` | driver |
| p256_fieldmul_compare | P-256 field multiply | `SC/X86Backend/P256FieldKernel.lean` | driver |
| p384_fieldmul_compare | P-384 field multiply | `SC/X86Backend/P384FieldKernel.lean` | driver |
| p384_compare | P-384 Montgomery multiply | `SC/X86Backend/Curve6MontMulProvenEmit.lean` | driver |
| sm2_compare | SM2 Montgomery multiply, two renders | `SC/X86Backend/Sm2MontMulKernel.lean` | builder `Com` |
| bls12381_compare | BLS12-381 Montgomery multiply | `SC/X86Backend/Curve6MontMulProvenEmit.lean` | driver |
| bls12381_fieldmul_compare | Montgomery REDC step | `SC/VIR/MontRedcEmit.lean` | builder `Com` |
| bls12381_g2_compare | Fp2 add, subtract, double and copy; G2 add and double | `SC/X86Backend/Bls12381G2.lean` | driver |
| bls12381_ppmap_compare | BLS12-381 Fp inverse | `SC/X86Backend/Bls12381PairingMap.lean` | driver |
| halo2_compare | Pallas and Vesta Montgomery multiply | `SC/X86Backend/PastaMontMulKernel.lean` | builder `Com` |
| s2n_montmul_compare | 4×4 → 8 limb bignum multiply | `SC/X86Backend/GenericEmit.lean` | driver |
| field_kernel_compare | ML-DSA NTT-8 | `SC/FieldNtt8EmitMldsa.lean` | front-generated |
| fhe_ntt_compare | FHE NTT (whole transform) | `SC/X86Backend/FheNttLoopEmit.lean` | front-generated |
| uov_compare | MAYO and UOV GF(256) MAC | `SC/VIR/MayoUovGf256Emit.lean` | builder `Com` |
| mpn_adx_owned_compare | mpn add_n and sub_n, ADX, n = 4, 8, 16, 32 | `SC/X86Backend/MpnAdxLprog.lean` over `SC/X86Backend/MpnAddFrontEmit.lean` | front-generated |
| mpn_cmp_front_compare | constant-time mpn compare | `SC/X86Backend/MpnCmpFrontEmit.lean` | front-generated |
| mpn_divqr_front_compare | mpn div_qr, Knuth D | `SC/X86Backend/MpnDivQrFrontEmit.lean` | front-generated |
| mpn_divrem_1_front_compare | mpn divrem_1 with precomputed inverse | `SC/X86Backend/MpnDivRem1FrontEmit.lean` | front-generated |
| mpn_mul_1_front_compare | mpn mul_1, runtime n | `SC/X86Backend/MpnMul1FrontEmit.lean` | front-generated |
| mpn_mulbase_front_compare | mpn mul_basecase, runtime n | `SC/X86Backend/MpnMulBasecaseFrontEmit.lean` | front-generated |
| mpn_shift_front_compare | mpn shift, runtime n | `SC/X86Backend/MpnShiftFrontEmit.lean` | front-generated |
| owned_bignum4_add_arrabi | four-limb add over the array ABI | `SC/X86Backend/Bignum4AddArrAbiDemo.lean` | builder `Com` |
| integration | rolled ADX add_n loops | `SC/X86Backend/MpnAddNAdxRolledFrontEmit.lean` | front-generated |
| regptr_out_probe | fixed-n multiply, add and subtract probes; Karatsuba schedules | `SC/VIR/RegPtrOutCallProbe.lean` with the `Mpn*FrontEmit` modules | front-generated |
| plonky3_compare | little-endian u64 serialization byte loop | `SC/Dialects/ByteMemrefRolledLoop.lean` | front-generated |
| gpu_compare | BabyBear multiply tile; MLIR and LLVM outputs, no assembly | `SC/MLIRBackend/ComToNvptx.lean`, `SC/TileBackend/ComToTileIR.lean` | builder `Com`, text output |

The scoreboard records no committed whole-protocol owned timer for ML-KEM-768 or
ML-DSA-65, and none for the SNOVA, UOV, MAYO or NTRU whole-protocol paths, whose
settled kernel figures are in table (A). The artifact-tied record disagrees for
two of those: it carries a UOV-Ip whole-sign at 1.850× against pqov with an owned
fraction of 55.3%, and a MAYO-1 whole-sign at 1.465× against MAYO-C AVX2, both
byte-identical to their references and both carrying a whole-protocol `rdtsc`
box-noise caveat. The 2026-09-15 reconciliation states them where they are
disputed and does not promote them into table (C).
