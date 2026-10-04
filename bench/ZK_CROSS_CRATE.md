# ZK provers: emitted-vs-production cross-crate head-to-head (#365)

End-to-end comparison of CatCrypt's verified-emitted ZK provers (the real-leaf
linkable binaries from #370, `bench/ZK_REAL_LEAF_BODIES.md`) against the
production Rust crates, on the same host.

**Host:** AMD Ryzen 7 PRO 7840U. All measurements `taskset -c 2` (refs) /
`taskset -c 2` (ours), min-of-reps, `rdtsc` cycles (AMD invariant-TSC, ~3 GHz;
cross-checked against `clock_gettime` wall time for Nova). Benches were run
sequentially, one core-pinned process at a time. C/Rust/cargo only; no Lean.

> **For the honest apples-to-apples ZK comparison, see
> [`ZK_PHASE_APPLES_TO_APPLES.md`](ZK_PHASE_APPLES_TO_APPLES.md).** Because the ZK
> provers' orchestration is partial/placeholder (full PCS, extension-field FRI,
> sum-check curve commits, single-binary emit), the apples-to-apples comparison is
> **phase-level**: the real-emitted kernels (Poseidon2 **0.87×** vs Plonky3, BN254
> pairing **1.12×** vs ark-marlin, BLS12-381 Groth16-verify pairing **1.22×** vs blst)
> are benched vs the production crate's **same** kernel; a whole-prover-vs-whole-prover
> ratio is **not** reported. The field-core-vs-full-prover rows below are component
> costs, NOT apples-to-apples — read them as such.

## Honest segregation (read this before the table)

Our emitted provers are **verified-emitted field-core + real leaves**, NOT
byte-for-byte production provers with every phase. Per #364/#367/#370:

- **Spartan / Jolt**: full sum-check **field core** (BabyBear Horner) + real
  verified Poseidon2 commit / challenger-squeeze / PCS-open leaves (and, for
  Jolt, the verified BabyBear Lasso grand-product). They do **not** include the
  polynomial-commitment **curve MSM** that the production Spartan prover runs.
- **Bulletproofs / Halo2**: full IPA fold **field core** (BabyBear) + gate
  constraint (Halo2) + real verified Poseidon2 Fiat-Shamir squeeze. The
  **vector-commitment curve MSM** is the documented residual (benched
  separately as a real Ed25519 MSM, see the MSM row).
- **Marlin**: the verifier's **pairing check is the REAL verified AUCurves
  BN254 optimal-ate pairing + Fp12 mul**; the sum-check round is the verified
  BN254 Fp Horner. The KZG-commit **G1 MSM** is the residual (the bn254 crate
  exposes no G1 group op; modelled at the Fp layer).

The reference crates are **full production provers** (every phase, including all
curve MSMs and commitments). So the rows below are **not** a like-for-like raw
ratio of the same computation; they state what each side actually computes.
Where a phase IS like-for-like (Marlin pairing check vs ark-marlin pairing
verify; the standalone real-curve MSM), that is called out as a true
apples-to-apples comparison.

## Reference crates: built vs skipped

| Crate | Version | Curve / field | Status |
|---|---|---|---|
| dalek bulletproofs | `bulletproofs 4.0` (+ `curve25519-dalek-ng`) | Ristretto255 | **built** |
| microsoft Spartan | `spartan 0.9` (`libspartan`) | curve25519 (Ristretto) scalar field | **built** |
| zcash halo2 | `halo2_proofs 0.3.2` | **Pasta** (vesta `EqAffine`) | **built** |
| arkworks Marlin | `ark-marlin 0.3` | BLS12-381 (KZG) | **built** |
| microsoft Nova | `nova-snark 0.23` | Pasta cycle (pallas/vesta) | **built** |
| a16z Jolt | `jolt 0.1.0` (crates.io) | — | **skipped** (see below) |

**Jolt (a16z) skipped — documented, not faked.** The `jolt` crate published on
crates.io (v0.1.0) is an **empty**: zero dependencies, a 1-line
`lib.rs`. The real a16z Jolt is a zkVM that lives only on GitHub and requires a
RISC-V guest toolchain on a Rust nightly plus a multi-GB build — infeasible on
this 14 GB host under the memory budget (≈4 GB free at bench time). Our emitted
"Jolt" prover (sum-check rounds + Lasso grand-product field core) is still
self-benched below; it just has no production-crate row to sit beside.

## Consolidated head-to-head

Numbers below are a fresh re-measure (`taskset -c 3`, AMD Ryzen 7 PRO 7840U,
`rdtscp`, min/median of the reps the binary runs internally), confirming the
prior pass reproduces. Each OURS prover is KAT-gated (deterministic, tamper
rejects, leaf primitive matches its Lean/published reference) before timing.

The OURS side now has **two rows per IPA/curve protocol**: a **field-core** row
(BabyBear sum-check/IPA + Poseidon2 Fiat-Shamir, no curve MSM) and a
**full-prover** row that wires the **real verified-curve 8-term MSM** commit
into the same body (the #378 work, KAT-gated against the verified Ed25519/curve
group). The field-core row is *not* the whole prover; the full-prover row adds
the commitment phase the production crate spends most of its cycles in.

| Protocol | OURS (verified-emitted) | what OURS computes | Reference (production) | what REF computes |
|---|---|---|---|---|
| **Spartan** (field core) | **136,448 cyc/prove** | 3 sum-check rounds: Poseidon2 commit + squeeze + BabyBear Horner (field core, no PCS MSM) | **microsoft-spartan: 13,170,696 cyc/prove** (cons=16, vars=16, NIZK) | full prover: sum-check + PCS curve MSM + FS |
| **Jolt** (field core) | **137,227 cyc/prove** | 3 sum-check rounds + Lasso grand-product (BabyBear field core) + Poseidon2 | *(no production row — crates.io crate is empty stub)* | — |
| **Bulletproofs** (field core) | **51,257 cyc/prove** | 3-round IPA fold recursion + Poseidon2 FS (BabyBear **field core**, no vector-commit MSM) | **dalek-bulletproofs: 14,979,822 cyc/prove** (n=32 range proof) | full prover: Pedersen vector commit (curve MSM) + IPA + FS |
| **Bulletproofs** (full prover) | **850,394 cyc/prove** | 8-term **real Ed25519 Pedersen MSM** commit + 3-round field IPA + Poseidon2 FS | **dalek-bulletproofs: 14,979,822 cyc/prove** (n=32 range proof) | full prover (n=32; OURS MSM is 8-term, so still smaller statement) |
| **Halo2** (field core) | **51,087 cyc/prove** | gate constraint + 3-round IPA fold + Poseidon2 FS (BabyBear **field core**, no Pasta MSM) | **halo2_proofs: 301,904,031 cyc/prove** (k=4, Pasta IPA) | full prover: gate + IPA fold + **Pasta curve MSM** + FS |
| **Halo2** (full prover) | **850,682 cyc/prove** | 8-term **real-curve MSM** commit + gate + 3-round field IPA + Poseidon2 FS (Pasta-exact leaf is the #377 seam, see below) | **halo2_proofs: 301,904,031 cyc/prove** (k=4, Pasta IPA) | full prover (k=4 Pasta; OURS MSM is 8-term Ed25519 stand-in) |
| **Marlin (prove)** | **(real BN254 KZG-commit MSM + pairing check + Fp sum-check)** — sub-rows below | — | **ark-marlin: 151,147,656 cyc/prove** (cons=25, BLS12-381) | full prover: AHP sum-check + KZG G1-MSM + opening |
| **Marlin (pairing check)** ★ | **20,386,533 cyc/check** | REAL verified BN254 optimal-ate pairing ×2 + Fp12 mul | **ark-marlin verify: 18,225,372 cyc/verify** | pairing-based KZG verify |
| **Marlin (Fp sum-check round)** | **474 cyc/round** | verified BN254 Fp 3-coeff Horner | *(folded into ark-marlin prove above)* | — |
| **MSM (real curve)** ★ | **797,649 cyc / 8-term** (99,706 cyc/term) | verified HACL\* **Ed25519** scalar-mul + point-add | *(the curve-MSM phase the field-core rows omit; the full-prover rows above include it; dalek/halo2 do it inline)* | — |
| **Nova** ‡ | *(no OURS analogue — we emit no folding prover)* | — | **nova-snark: ~2,178 cyc / 762 ns per folding step** | one Pasta-cycle `prove_step` (trivial step circuit) |

★ = **true apples-to-apples on this phase.** The Marlin pairing-check row is the
strongest result: our verified BN254 pairing check (**20.4M cyc**) is within ~12%
of ark-marlin's full BLS12-381 pairing-based verify (**18.2M cyc**) — same
2-pairing structure, comparable cost, and ours is the formally-verified pairing.
(Curve differs: ours BN254 vs ark BLS12-381; both ~254/255-bit pairing-friendly.)
The standalone real-curve MSM row gives the honest curve-MSM cost; it is the same
8-term MSM that the Bulletproofs/Halo2 **full-prover** rows now include inline.

‡ Nova is a **folding** scheme with **no analogue** in our emitted set. The
2,354 ns/step is a same-host figure but the workload is a *trivial* step
circuit (the ~10k constraints are recursion-verification overhead; the per-step
fold is over near-zero witnesses), so it is a **lower bound** on Nova folding
cost, not a representative MinRoot/real-circuit step. Reported as a reference
data point only.

### How to read the field-core vs full-prover rows

The Spartan/Jolt/Bulletproofs/Halo2 **field-core** OURS numbers (50k–140k cyc) are
**two to three orders of magnitude smaller** than the production crates (13M–302M
cyc) because **they are not computing the same thing**: the production provers
spend the overwhelming majority of their cycles in **curve MSMs / polynomial
commitments over a 255-bit group**. The field-core rows are the cost of the
**verified field-arithmetic core + Fiat-Shamir** of each protocol *only*.

The **full-prover** rows (Bulletproofs/Halo2 ≈850k cyc, Marlin's KZG-commit MSM
sub-row) fold the **real verified-curve 8-term MSM** commit into the same body —
that is the phase production crates spend their time in, now actually computed and
KAT-gated. The remaining honest gaps to true production parity are: (a) the OURS
statement is small (8-term MSM / 3 IPA rounds vs the crate's n=32 / k=4 / cons=25
circuits), so OURS still does **less work**; and (b) the curve is an **Ed25519
stand-in** for Bulletproofs/Halo2 (the Pasta-exact group leaf is the #377 seam,
see below), not the protocol-exact group. A fair mental model:

> OURS field-core (≈55k–140k cyc) **+** real curve MSM (≈100k cyc/term × #terms)
> ≈ the full-prover rows ≈ the regime the production prover spends most of its
> time in (at the OURS statement size, which is smaller than the crate's).

Do **not** read e.g. "Halo2 field-core 51,087 vs 301,904,031" as a ~6000× speedup
— it is a field-core-vs-full-prover comparison, and the MSM gap is real and
documented; the full-prover row (850k) is the honest one to weigh, and it is
still a smaller statement than halo2's k=4 Pasta circuit.

## The Spartan matched-work number (and the honest residual)

A separate, fuller like-for-like Spartan comparison (`../SSProve-lean/bench/spartan_compare/`,
tasks #429/#431/#435) measures CatCrypt's clause-for-clause prover
(`spartan_prover_prod_kat.c`: 2 Hyrax 4×4 commits + dot-product-opening IPA +
the full two-phase R1CS sum-check + the intermediate ZK sub-proofs +
Poseidon2 Fiat-Shamir, all at `num_vars=16`) against `microsoft-spartan`
(`spartan 0.9`, `NIZK::prove`) at the **same statement size**
(`num_cons=16, num_vars=16`):

| Prover | cyc/prove |
|---|---|
| OURS (2 Hyrax 4×4 + IPA open + two-phase sum-check + **ProductProof + 2 EqualityProofs** + FS) | 8.94M |
| microsoft-spartan (`NIZK::prove`) | 13.22M |
| ratio OURS / microsoft-spartan | **0.68×** |

**This is the honest matched-work number.** An earlier version of this row read
0.50×; #436 flagged it as an apples-mismatch (OURS did strictly less curve work
and truncated the MSM scalars to 64 bits). #435 fixed both:

- **Scalar fidelity.** OURS now feeds full-width 256-bit Ristretto scalars to
  the curve MSM (`set_scalar_fq`, four 64-bit limbs of the `fq` field) and the
  IPA fold uses the real field challenge `u` and its modular inverse
  `u^{-1}=u^{q-2}` (the prior `set_scalar`/`& 0xffff`/`& 0xffffffffu` masks are
  gone). This does not change per-`point_mul` cost (HACL*'s `point_mul` is a
  constant-time **variable-base** ladder iterating all 256 bits regardless of
  magnitude) but makes the MSM semantics honest.
- **Intermediate ZK sub-proofs replicated (clause (c)).** OURS now runs the
  `ProductProof` over `Az_claim·Bz_claim` (6 Pedersen commits) and the two
  phase-closing `EqualityProof`s (2 commits + an `r·H` each), clause-for-clause
  from `spartan-0.9.0/src/nizk/mod.rs`. The scalar outputs are KAT'd
  byte-identical against the libspartan reference `spartan_nizk_ref`
  (`bench/zk_refs/spartan_ref/src/nizk_ref.rs`, over `curve25519-dalek-ng`); the
  commitments run over the verified Ed25519 group.

Adding clause (c) raised OURS from 6.5M to 8.94M, so the ratio rose from the
artifact **0.50× to 0.68×** — the rise toward parity #436 predicted.

**Why OURS is still somewhat ahead (the named residual).** libspartan's ZK
sum-check (`sumcheck.rs::prove_cubic_with_additive_term` phase-1 / `prove_quad`
phase-2) commits *every* round polynomial to the curve (`poly.commit`, a
`vartime_multiscalar_mul`), commits a per-round eval, and runs a per-round
`DotProductProof::prove` — in each of the 9 rounds. OURS reproduces those round
polynomials' *coefficients* **byte-identically** (`spartan_twophase_fq.h`,
KAT-gated against `twophase_ref.rs`) but over a 4×64-bit Barrett mod-`q` field
with **zero curve operations per round**, doing the commitment/opening MSMs
once. That per-round sum-check curve work is the remaining gap; replicating it
(a much larger item than clause (c)) — or, equivalently, giving microsoft-spartan
a non-ZK field-only sum-check — would close the last 0.68×→parity. The
`KnowledgeProof` for `Cz_claim` (one more constant-size commit) is also still
omitted.

**The verified-compiler contribution** is that OURS's field core (BabyBear
sum-check) and Poseidon2/curve leaves are emitted/verified, and the sum-check +
intermediate-proof scalar arithmetic is byte-identical to libspartan — not that
the prover is intrinsically faster.

**Where fixed-base does / does not apply across the ZK suite.** No prover in
this suite uses a fixed-base comb. Every curve MSM here goes through the same
constant-time **variable-base** HACL* Ed25519 ladder (the #370 leaf, lane =
`point_mul`): Spartan's Hyrax commits + IPA, the Bulletproofs Pedersen vector
commit + IPA, and the Halo2 commit. The standalone "MSM (real curve)" row
(≈100k cyc/term) is the honest per-term variable-base cost shared by all of
them. So the fixed-base lever is **not** the explanation anywhere; the
cross-protocol pattern is instead **how many variable-base scalar-mults each
prover issues at the benched statement size**, which is why Bulletproofs (full
prover, n=32 range proof, many MSM terms) is **2.15× behind** while Spartan
(few curve terms after we move the sum-check off-curve) is ahead.

## Pasta-MSM status (step 4) — SUPERSEDED: the Pasta-exact group IS now own-emitted

The Halo2-vs-zcash row's protocol-exact group is **Pasta** (pallas/vesta). The
note that follows recorded the state *before* the Pasta group was emitted; it is
kept for provenance but is **superseded by #427/#430/#436/#480**:

- **(Superseded) "Not feasible in this pass."** The earlier blocker was that the
  only linkable AUCurves Pasta artifact was the **base-field inverter**
  (`vesta_invert_divstep_sat`), with the Pasta **group** point-add/scalar-mul
  excluded from the AUCurves dune build. That sent the Halo2 row to the #370
  Ed25519 stand-in.

- **CURRENT (own-emitted, KAT'd vs the #377 Rocq oracle).** The protocol-exact
  Pasta (Pallas) **group** *is* now built and runs over a fully
  **own-compiler-emitted** Pallas base field — there is **no Ed25519 stand-in**
  for the Halo2 commitment any more:
  - `../SSProve-lean/bench/halo2_compare/pasta_msm_av.c` — the Pallas affine group law +
    scalar-mul + 8-term commit MSM.
  - `../SSProve-lean/bench/halo2_compare/pasta_field_ownemit.c` — the `pallas_fp_*` field over
    OUR emitted leaves: `pasta_emit_mul_4_8` (256×256 product, owned-x86
    `mul48Block`, #430), `pasta_mont_redc_4` (Montgomery reduce, #436/#445),
    `pasta_field_{add,sub}` (hardware ADD/ADC+CMOV, #480),
    `safegcd_divstep62_invert_k4 @ p_pallas` (inverse, #258/#436).
  - KAT `pasta_ownemit_kat` reproduces the #377 Rocq `Pasta_MSM` vectors
    (G2/G3/G5, `[2]G+[3]G=[5]G`, `msm`, on-curve) and the 8-term Halo2 commit is
    homomorphic + on-curve. **PASS** (re-run this session).
  - Live phase number (`pasta_ownemit_msm_phase_bench`, `taskset -c 3`,
    min-of-5): **~245k cyc / 8-term commit MSM** (243k–250k across runs, ~30k
    cyc/term variable-base), safegcd inverse ~8k cyc. This is the protocol-exact
    Pasta group, not the stand-in.
  - Lean realization tie: `CatCrypt/Crypto/ZK/Halo2PastaFieldEmit.lean`
    (`pastaMontMul_realizes_mul`, `pastaAffineAdd_realizes`) +
    `Halo2PastaFieldConnect.lean` connect the emitted field to
    `Halo2.halo2_uc_secure`'s `pallas_add`/`pallas_smul`. Axiom-clean.

  So the Halo2 commitment MSM phase **was a wiring/stale-doc gap, not unbuilt**:
  the Pasta-exact own-emitted MSM is the canonical leaf; the Ed25519 stand-in row
  remains only as the legacy `halo2_prover_kat` field-core path. The **named
  residual is unchanged**: the IPA / DLOG knowledge-soundness reduction
  `Halo2_IPA_KnowledgeSoundness_at` (catalog #366).

## Reproduce

OURS binaries (field core, from #370): `../SSProve-lean/bench/spartan_compare/spartan_prover_kat`,
`../SSProve-lean/bench/jolt_compare/jolt_prover_kat`,
`../SSProve-lean/bench/bulletproofs_compare/ipa_prover_kat`,
`../SSProve-lean/bench/halo2_compare/halo2_prover_kat`. OURS full-prover (real curve MSM, #378):
`../SSProve-lean/bench/bulletproofs_compare/ipa_prover_full_kat`,
`../SSProve-lean/bench/halo2_compare/halo2_prover_full_kat`,
`bench/bn254_compare/target/release/marlin_prover_kat`,
`bench/msm_compare/msm_real_curve_kat`. Each prints a `*-self-bench` cyc line
after its KAT gate. Run each under `taskset -c 3`.

Reference crates: `bench/zk_refs/{bulletproofs,spartan,halo2,marlin,nova}_ref/`.

```
cd bench/zk_refs/<crate>_ref && cargo build --release
taskset -c 3 ./target/release/<crate>_bench
```

The numbers in the tables above were re-confirmed `taskset -c 3` (#365); they
reproduce within run-to-run variance of the prior `-c 2` pass.
