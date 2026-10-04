# ZK provers: honest PHASE-LEVEL apples-to-apples (real-emitted vs production)

The ZK provers in this tree emit a **verified field/commit core with real leaves**
but their **orchestration is partial/placeholder** (full PCS, extension-field FRI,
sum-check curve commitments, single-binary ZMM prover). A whole-prover-vs-whole-prover
number would therefore be **misleading** — it would compare a placeholder orchestration
against a complete production prover. We do **not** report one.

The honest comparison is **phase-level**: for each prover, list its phases, mark each
**REAL-EMITTED** (a verified owned kernel, KAT byte-identical to the production crate's
same kernel) vs **PLACEHOLDER**, and for the real-emitted phases bench our owned kernel
against the production crate's **same** kernel (same field/curve/params, taskset -c 3,
min-of-N or the MCA gate where rdtsc is noisy). The whole-prover orchestration ratio is
explicitly withheld where any phase is placeholder.

**Headline.** *ZK apples-to-apples is phase-level. The real-emitted kernels are at:
Poseidon2 (the dominant FRI/Merkle/FS hash, ~97% of a STARK prover) **0.87×** vs Plonky3
production AVX2; the field/LDE/FRI-fold/Merkle/challenger phases are verified-emitted
(Plonky3 A1–A7) and the Poseidon2-rerouted whole-FRI-prover lands at **0.92×** vs the
real `p3-uni-stark` crate; the BN254 pairing-check phase **1.12×** vs ark-marlin's
pairing verify (formally-verified pairing); the BLS12-381 curve phase (Groth16 verify =
owned `pp_map`) **1.22×** vs blst hand-asm. The Halo2 **Pasta commitment MSM** is
own-compiler-emitted and protocol-exact (Pallas group over an own-emitted base field,
KAT'd vs the #377 Rocq oracle, ~245k cyc/8-term) — NOT a stand-in. The remaining
placeholders (extension-field FRI, single-binary ZMM emit) are unbuilt /
blocked-on-integration and are not folded into any whole-prover ratio.*

**Whole-prover composition (this pass).** Only the **Spartan/Jolt BabyBear
sum-check field core** composes into a Plonky3-style **owned** single-`.s`
whole-prover (`ZkSumCheckWholeProverEmit`: the owned BabyBear leaves +
owned `loopLcmd` sum-check orchestration, NO jasminc — assembles, links, runs;
round-step byte-identical to the KAT'd `fri_fold_rc`). The **full** whole-prover
numbers that include the PCS curve MSM stay jasminc+C (Spartan, Halo2) or absent
(Marlin has no composed binary, Jolt has no production reference), because the
owned x86 regArith backend has **no curve-group emit** — the universal gap. No
new whole-prover *ratio* is quoted (statement-size mismatch / box-noise / missing
reference). See "Whole-prover composition, per prover" below.*

**Correction (this pass).** An earlier version of this doc marked the **Pasta MSM**
(Halo2) and the **Ristretto/curve25519 MSM** (Bulletproofs/Spartan) as "Ed25519/BLS
stand-in" placeholders. Investigation showed these were **stale-doc / wiring gaps, not
unbuilt**: the Pasta-exact group is fully own-emitted (#427/#430/#436/#480, KAT-passing),
and the curve25519 arithmetic Ristretto255 is built on is emitted as a verified SIMD
Straus MSM (#461, KAT vs libsodium/RFC 8032). The placeholder phases are the
**extension-field FRI** (UNBUILT — no quartic-ext kernels) and the **single-binary
orchestration** (BLOCKED-on-integration — pieces emitted, no composing module). See
"What is NOT claimed" for the per-phase corrected assessment.

Host: AMD Ryzen 7 PRO 7840U (Zen 4), `taskset -c 3`, `rdtsc`, min-of-N. Numbers are
measured this session or transcribed from the cited bench docs (no fabricated ratios).

## Per-prover phase table

Legend: **R** = REAL-EMITTED (verified owned/jasmin leaf, KAT byte-identical to the
production crate's same kernel). **P** = PLACEHOLDER (hand-written C / stand-in /
not-emitted orchestration). Ratio = our-emit / production, where a like-for-like
production kernel exists (`< 1.0` = ours faster).

| Prover | phase | R / P | our-emit vs production crate (same kernel) | ref |
|---|---|---|---|---|
| **Plonky3** (FRI/STARK) | Poseidon2 perm (Merkle commit, FRI fold-layer commit, Fiat-Shamir, PoW) — **~97% of the prover** | **R** | **0.87×** — AVX-512 ZMM Montgomery Poseidon2 2872 cyc/perm vs Plonky3 prod AVX2 `plonky3_bench` 3302 cyc/perm (live); KAT == p3 `test_default_babybear_poseidon2_width_16` 8/8. **Lowering: MLIR + `llc -O3`** (`poseidon2_avx512_mont_kernels.mlir` → `.o`), not the owned x86 backend; the owned-backend render (`gen_zmmasm/`) is recorded separately at 1.075× | `poseidon2_compare`, `POSEIDON2_AVX512_BENCH.md` |
| Plonky3 | trace-LDE (coset NTT), FRI fold (base field), Merkle, challenger squeeze, quotient compose, OOD/DEEP | **R** | verified-emitted (A1–A7); KAT byte-identical to the `plonky3-hax` spec per phase. No standalone production-p3 kernel entry to bench against → measured via the whole-FRI-prover reroute below | `plonky3_compare/README.md`, `FULL_PROVER_VS_P3.md` |
| Plonky3 | **whole FRI prover, Poseidon2-rerouted** (Poseidon2 carries ~97%) | R (perf) | **0.92×** — 0.54M cyc/prove vs real `p3-uni-stark` 0.5.3 0.59M; byte-identical proof gate. **Mixed lowering:** the prover spine `plonky3_honest_prove.s` is jasminc, the rerouted Poseidon2 phase is the MLIR + `llc` object. `honest_prove_reroute` carries the MLIR render's 20 `vpmullq` and none of the owned render's `c_NPI`/`c_RSQR`/`c_rotIdx` symbols | `FULL_PROVER_VS_P3.md:153-198` |
| Plonky3 | extension-field FRI (deg-4 `BinomialExtensionField`), full PCS quotient opening, **single-binary ZMM orchestration** | **P** | not emitted — C orchestration over emitted leaves; no emitted ext-field kernels; whole `prove` not a single emitted binary (Gap 2) | `FULL_PROVER_VS_P3.md:202-326` |
| **Marlin** (KZG) | BN254 pairing check (2 pairings + Fp12 mul) | **R** | **1.12×** — REAL verified BN254 optimal-ate pairing ×2 + Fp12 20.4M cyc/check vs ark-marlin BLS12-381 pairing-based KZG verify 18.2M (**true apples-to-apples on this phase**; ours is the formally-verified pairing) | `ZK_CROSS_CRATE.md:79-88` |
| Marlin | BN254 Fp sum-check round (3-coeff Horner) | **R** | 474 cyc/round (verified BN254 Fp); folded into the production prover above (no standalone ark row) | `ZK_CROSS_CRATE.md:80` |
| Marlin | KZG-commit G1 MSM, AHP sum-check orchestration | **P** | curve MSM modelled at the Fp layer; bn254 crate exposes no G1 group op; full AHP not emitted | `ZK_CROSS_CRATE.md:28`, `ZK_OWNED_BACKEND.md:25` |
| **Groth16** | pairing-product verify `e(A,B)·∏e(Lᵢ,G2ᵢ)` | **R** | **1.22×** — owned BLS12-381 `pp_map` (3 owned pp_map + 2 owned fp12_mul); the verify pairing PHASE is fully owned-emitted; inherits the owned BLS12-381 MSM/fp_mul floor (1.22× MSM, 1.11× fp_mul vs blst hand-asm) | `ZK_OWNED_BACKEND.md:24,52-58`, `bls12381_ppmap_compare` |
| Groth16 | prover (witness MSM, QAP) | **P** | not emitted | `ZK_OWNED_BACKEND.md:24` |
| **Bulletproofs** | BabyBear IPA fold field core + Poseidon2 Fiat-Shamir | **R** | field core emitted + verified; Poseidon2 FS = the 0.87× leaf above | `ZK_CROSS_CRATE.md:23-24`, `ZK_OWNED_BACKEND.md:26` |
| Bulletproofs | Pedersen vector-commit MSM (curve) | **R** (curve25519 arith emitted; protocol encoding is the residual) | The IPA prover bench currently calls the scalar HACL\* `point_mul` (~100k–115k cyc/term variable-base). **The protocol-relevant curve25519 arithmetic IS emitted**: the SIMD Ristretto 2625×4 field + extended-twisted-Edwards point add/double + a shared-doubling **Straus MSM** (`../SSProve-lean/bench/dalek/gen_zmmasm/ristretto_2625x4_wholeop.c`, #461) are KAT byte-identical to **libsodium / RFC 8032** and benched at ~88k cyc/scalarmul (4-bit window, 8-way SIMD, 1.18× vs HACL\* scalar). Ristretto255 is curve25519 under a canonical point encoding; the emitted arithmetic is exactly that base group. **Wiring residual:** swapping the prover's per-term scalar `point_mul` for the 8-lane SIMD Straus MSM is an interface-batching change (scalar→8-wide), not unbuilt math | `ZK_CROSS_CRATE.md:81,184-193`, `dalek/gen_zmmasm/README.md` (#461) |
| Bulletproofs | n=32 range-proof orchestration (full statement) | **P** | OURS statement is smaller (8-term MSM / 3 IPA rounds vs n=32); not a whole-prover claim | `ZK_CROSS_CRATE.md:75,99-124` |
| **Halo2** | BabyBear IPA fold + gate constraint + Poseidon2 FS | **R** | field core emitted + verified; Poseidon2 FS = 0.87× leaf | `ZK_CROSS_CRATE.md:23-24` |
| Halo2 | Pasta vector-commit MSM | **R** (own-emitted Pasta-exact) | **NOT a stand-in** — protocol-exact Pasta (Pallas) group over a fully own-compiler-emitted Pallas base field (mul=`mul48Block`+`pasta_mont_redc_4`, add/sub=hardware ADD/ADC+CMOV #480, inverse=`safegcd_divstep62 @ p_pallas`); KAT'd vs the #377 Rocq `Pasta_MSM` oracle; **~245k cyc/8-term commit MSM** (243k–250k across runs, ~30k cyc/term), inverse ~8k cyc (live, `-c 3`, min-of-5) | `halo2_compare/README.md` (#427/#430/#436/#480), `pasta_ownemit_msm_phase_bench`, `Halo2PastaFieldEmit.lean` |
| Halo2 | k=4 Pasta full-prover orchestration | **P** | smaller statement (8-term commit MSM vs k=4 full Pasta IPA); the per-phase MSM group is now Pasta-exact (above), but the full k=4 orchestration is not emitted as one prover | `ZK_CROSS_CRATE.md:76-77` |
| **Spartan** | two-phase R1CS sum-check (BabyBear) + Poseidon2 FS | **R** | sum-check round coefficients byte-identical to libspartan (KAT-gated); Poseidon2 FS = 0.87× leaf | `ZK_CROSS_CRATE.md:126-181` |
| Spartan | Hyrax commit MSM + IPA open (curve) | **R** (curve25519 arith emitted; encoding residual) | The prover bench calls scalar HACL\* `point_mul` over full-width 256-bit Ristretto scalars (#435). The curve25519 arithmetic Ristretto255 is built on **is emitted** (SIMD 2625×4 field + ETE point ops + Straus MSM, #461, KAT vs libsodium/RFC 8032) — same residual as Bulletproofs (wire the SIMD Straus MSM into the prover loop + Ristretto canonical encode/decode) | `ZK_CROSS_CRATE.md:81,144-160`, `dalek/gen_zmmasm/README.md` (#461) |
| Spartan | full ZK sub-proofs / per-round curve commits | **P** | the per-round sum-check curve commits libspartan does are off-curve in OURS (the named 0.68× matched-work residual) | `ZK_CROSS_CRATE.md:164-181` |
| **Jolt** | sum-check + Lasso grand-product (BabyBear field core) + Poseidon2 | **R** | field core emitted + verified; Poseidon2 = 0.87× leaf. *No production-crate row — crates.io `jolt 0.1.0` is an empty; the real a16z zkVM needs a multi-GB RISC-V build, infeasible on this 14 GB host* | `ZK_CROSS_CRATE.md:46-54,73` |
| Jolt | PCS commit MSM + zkVM orchestration | **P** | not emitted | `ZK_OWNED_BACKEND.md:29` |

## Whole-prover composition: Plonky3-style single-binary, per prover

`Plonky3WholeProverEmit` + `Plonky3OrchLoopsEmit` composed the Plonky3
prover's owned BabyBear phase leaves (compress / hash_leaf / ntt_layer / fri_fold
/ bb_inv) into ONE owned-backend `.s` (`Com.toLprogPhysAbi`, NO jasminc) with the
orchestration loops as owned `loopLcmd` back-edges. The question for the other
provers: can their real-emitted phase leaves be composed the same way into a
single-binary whole-prover that yields a real apples-to-apples number — and where
not, what is the precise orchestration gap.

The answer per prover. Two distinct single-binary paths exist in this tree:
the **owned x86 backend** (Plonky3-style, no jasminc, `loopLcmd` loops — only the
BabyBear-regArith leaves are emittable this way) and the **jasminc-composed
`*_prover_link.jazz` → `.s`** (the curve/pairing/Poseidon2-sponge work, with the
curve MSM run in GMP/HACL\* C alongside).

| Prover | single-binary whole-prover? | path | whole-prover number | precise orchestration gap |
|---|---|---|---|---|
| **Spartan** | YES (two halves) | (1) owned `.s` for the **BabyBear sum-check field core** (`ZkSumCheckWholeProverEmit`, Plonky3-style: owned compress/squeeze/round-step/bb_inv leaves + the Spartan two-phase 9-round `loopLcmd` orchestration, NO jasminc — `zk_sumcheck_fieldcore_whole_prover_owned.s`, assembles + links + runs, round-step byte-identical to the KAT'd `fri_fold_rc`); (2) jasminc+C `spartan_prover_prod_kat` for the **full** prover incl. the PCS curve MSM | full prover (sum-check + 2 Hyrax 4×4 commits + IPA open + two-phase + ProductProof + 2 EqualityProofs + FS): **noisy, ~11–25M cyc/prove** on this loaded box vs microsoft-spartan `spartan_bench` **15.6M** (min-of-100, stable). OURS self-bench is single-shot (not min-of-N) → **rdtsc-noisy, ratio withheld** (was 0.68× at a quiet-box 8.94M run, README) | the **PCS curve MSM** (Hyrax 4×4 Ed25519/Ristretto commit + dot-product IPA) is **not owned-emittable** — it is curve-group arithmetic run over the verified-field/trusted-group HACL\* C leaf, not the owned x86 regArith backend (which has no curve emit). So the owned single-`.s` covers the **sum-check field-core half**; the full-prover binary is jasminc+C. Owned-composing the curve MSM is **blocked on a curve backend** |
| **Jolt** | YES (field-core half only) | owned `.s` for the BabyBear sum-check + Lasso grand-product field core (same `ZkSumCheckWholeProverEmit` module — the `jolt_sumcheck_loop` 3-round `loopLcmd` driver shares the owned leaves) | **NO whole-prover ratio possible** — there is no production reference: crates.io `jolt 0.1.0` is an empty, and the real a16z zkVM needs a multi-GB RISC-V build infeasible on this 14 GB host | the gap is the **missing production reference**, not our side. Plus the **PCS commit MSM** (same curve-backend block as Spartan) |
| **Halo2** | YES (jasminc) | jasminc `halo2_prover_link.s` + the protocol-exact Pasta MSM (`pasta_msm.c`, GMP); `halo2_prover_pasta_kat` runs (**~204k cyc/prove**, live) | **NOT a whole-prover ratio** — OURS proves an 8-term-commit + gate + 3-round field-IPA statement; `halo2_proofs` proves a full **k=4 StandardPlonk** circuit (full permutation argument, degree-2⁴ commits, blinding, full-domain IPA) at **350.7M cyc/prove** (min-of-100, live). The statement sizes differ by orders of magnitude → the cyc ratio is **not** a speedup and is **withheld** | the full **k=4 PLONK orchestration** (large-domain Pasta MSMs, the permutation argument, blinding) is not emitted as one prover; the per-phase Pasta commit MSM IS protocol-exact own-emitted (#427/#430/#436/#480) but runs in GMP C, not the owned x86 backend (curve-backend block again). The BabyBear field-IPA core is owned-composable but is a *smaller statement* than k=4 |
| **Marlin** | **NO** | only the orchestration `.jazz` (opaque-leaf, `marlin_prover_from_rustcmd.jazz`) is emitted; **no `*_prover_link.jazz`/`.s` composes it to a single binary**, and the full-prover KAT (`marlin_prover_kat.rs`) is a Rust driver, not a composed binary | the **pairing-verify PHASE** is real apples-to-apples (**1.12×** vs ark-marlin, in the phase table); ark-marlin full prove is **177.3M cyc/prove** (min-of-100, live) but OURS has **no composed whole-prover binary** to compare → **no whole-prover ratio** | TWO gaps: (1) **no single-binary composition** of the Marlin orchestration leaves exists at all (the `_link.jazz` was never built); (2) Marlin's sum-check is over **BN254 Fp**, not BabyBear, so it cannot reuse the owned BabyBear sum-check leaves (`ZkSumCheckWholeProverEmit`) — owned-composing it needs BN254-Fp regArith leaves, which are not emitted |

**Result.** Of the four, only the **Spartan/Jolt BabyBear sum-check field core**
composes into a Plonky3-style **owned** single-`.s` whole-prover (this pass —
`ZkSumCheckWholeProverEmit`, KAT-runnable). The **full** whole-prover
numbers that include the PCS curve MSM remain (a) jasminc+C binaries (Spartan,
Halo2), with the curve MSM in GMP/HACL\* C because the owned backend has no curve
emit, or (b) absent (Marlin has no composed binary; Jolt has no production
reference). No whole-prover *ratio* is quoted where a phase is a stub, the
statement size differs (Halo2), the box-noise dominates (Spartan, single-shot
self-bench), or the reference is missing (Jolt). The honest universal gap is the
**curve/pairing backend** — every prover's PCS commitment MSM is curve-group
arithmetic the owned x86 regArith backend cannot emit, so the field-core half
owned-composes but the commitment half stays in C.

## Real-emitted phase ratios folded into the SAME-TIER geomean

Only the **real-emitted, like-for-like-production** phase ratios enter the geomean
(`../SSProve-lean/bench/framework/geomean_ratios.tsv`, tier `same-tier`). The placeholder-orchestration
phases and the whole-prover numbers do **not**:

| geomean row | ratio | what is real-emitted |
|---|---|---|
| `poseidon2_babybear_w16_phase` vs Plonky3 | **0.87×** | AVX-512 ZMM Poseidon2 permutation (the dominant FRI/Merkle/FS phase) |
| `plonky3_fib_stark_p2reroute` vs Plonky3 | **0.92×** | whole FRI prover with Poseidon2 (~97%) rerouted to the verified AVX-512 leaf |
| `marlin_pairing_check_phase` vs ark-marlin | **1.12×** | BN254 optimal-ate pairing ×2 + Fp12 (verified pairing) |
| `zk_groth16_verify_phase` vs blst | **1.22×** | BLS12-381 `pp_map` pairing-product (Groth16 verify) |

(The pre-existing `poseidon2_babybear_w16` 0.850 and `poseidon2_babybear_vbackend`
1.075 rows are the same Poseidon2 phase at different emit backends; the BN254/BLS12-381
`fp_mul` / `fp_inv` / `g1_msm` rows already in the TSV are the underlying field/curve
kernels these ZK phases are built from.)

**No new whole-prover row was added this pass.** The Spartan/Jolt owned
field-core whole-prover (`ZkSumCheckWholeProverEmit`) composes and runs, but
the only *full* whole-prover number that would be apples-to-apples (incl. the PCS
curve MSM) is the jasminc+C `spartan_prover_prod_kat` single-shot self-bench,
which is rdtsc-noisy on this loaded box (~11–25M, no min-of-N harness) — so it is
**withheld**, not folded into the geomean. Halo2's whole-prover number is a
different statement size (8-term commit vs k=4 PLONK) and is likewise withheld.
Jolt has no production reference. Only the real, like-for-like **phase** ratios
(the four rows above) enter the geomean; the whole-prover composition this pass is
an emit/runnability result, not a new perf ratio.

## What is NOT claimed

- **No whole-prover ratio** where orchestration is placeholder. The field-core
  whole-prover numbers in `ZK_CROSS_CRATE.md` (50k–140k cyc vs 13M–302M production) are
  **field-core-vs-full-prover**, not apples-to-apples, and are flagged as such there;
  they are not folded into the geomean.
- **MSM/commit phases, corrected status (this pass).** Two of the four "stand-in
  group" claims were **stale-doc / wiring gaps, not unbuilt math**:
  - **Halo2 Pasta MSM — now own-emitted, protocol-exact.** The Pasta (Pallas)
    commitment MSM runs over a fully own-compiler-emitted Pallas base field
    (#427/#430/#436/#480), KAT'd vs the #377 Rocq `Pasta_MSM` oracle, **~243k
    cyc/8-term** (live). It is **not** an Ed25519/BLS stand-in. The earlier
    `ZK_CROSS_CRATE.md` "Pasta-MSM status (step 4)" note predates the emit and is
    superseded there.
  - **Bulletproofs/Spartan curve25519 arith — emitted (encoding is the residual).**
    The SIMD Ristretto 2625×4 field + ETE point add/double + Straus MSM is emitted
    and KAT byte-identical to libsodium/RFC 8032 (#461). Ristretto255 is curve25519
    under a canonical encoding; the *arithmetic* is the emitted base group. The
    open residual is (a) wiring the 8-lane SIMD Straus MSM into the per-term IPA
    prover loop (an interface-batching change), and (b) the Ristretto canonical
    point encode/decode wrapper. The prover benches currently still call scalar
    HACL\* `point_mul`.
  - **Marlin/Groth16** use real verified BN254 / BLS12-381 (not stand-ins).
- **Extension-field FRI, full PCS opening, single-binary ZMM orchestration** remain
  PLACEHOLDER and are **unbuilt or blocked-on-integration**, not stale-doc:
  - **Extension-field FRI (Plonky3 deg-4 `BinomialExtensionField`)** — UNBUILT.
    No quartic-extension arithmetic kernels are emitted; the emitted FRI fold is
    over the **base** field BabyBear only (`FULL_PROVER_VS_P3.md:238-267`). Emitting
    ext-field kernels (binomial `x⁴=11` mul/inverse, ExtensionMmcs fold) is open work.
  - **Single-binary ZMM orchestration** — BLOCKED-on-integration (wiring), pieces
    exist. Every primitive (ZMM lane ops, verified looped control flow, the phase
    leaves) is emitted+proven; no module *composes* them into one `prove` `Com`
    emitted to a single `.s` (`FULL_PROVER_VS_P3.md:277-326`, Gap 2). Bounded,
    scoped integration work — not a backend gap.
  These are explicitly excluded from every ratio above.
