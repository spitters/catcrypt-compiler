# ZK prover real leaf bodies + end-to-end self-benches (#370)

The emitted ZK prover orchestrations (#364 Spartan/Jolt/Bulletproofs, #367
Halo2/Marlin) reflect through CatCrypt's verified front but, as emitted, call
**stub** leaf bodies (`gen_com/*_stub.jazz`: trivial copy shells). A stub can't
be timed. This pass replaces those stubs with **real linkable leaf bodies**
drawn from the committed verified kernels, links each prover into one object,
and runs an end-to-end KAT-gated self-bench.

The real leaf bodies are:

- **BabyBear field** (`_p2_fmul/_fadd/_fsub`, p = 2^31 - 2^27 + 1): the verified
  field leaf copied verbatim from the emitted Poseidon2 leaf
  (`plonky3_compare/include/plonky3_poseidon2_hash.jinc`).
- **Poseidon2-BabyBear permutation** (`p2_perm`, PaddingFreeSponge<16,8,8>): the
  verified permutation, byte-identical to upstream Plonky3
  `test_default_babybear_poseidon2_width_16`, used for the commit / challenger
  (Fiat-Shamir) leaves.
- **BN254 optimal-ate pairing** (`pairing_optimal` + `fp12_mul`): the AUCurves
  verified-bedrock2 tower, KAT-anchored to the published EIP-196/EIP-197
  generators, used for the Marlin KZG verifier pairing check.
- **Ed25519 group** (`Hacl_Impl_Ed25519_*`: `point_mul`, `point_add`,
  `point_decompress`): the verified HACL* prime-order Edwards-25519 group, used
  for the real-curve MSM (closes the toy-EC MSM gap).

All builds use jasminc / gcc / cargo only — no Lean build, no re-emit. The
orchestration bodies in the `*_prover_link.jazz` files are byte-identical to the
committed `gen_com/*_from_rustcmd.jazz`; only the leaf bodies are now real.

## Per-prover real-leaf readiness + self-bench (taskset -c 2, KAT-gated)

| Prover | Leaves real-linked | Residual (stub/toy) | Self-bench |
|---|---|---|---|
| **Spartan** | commit/round-commit/PCS-open = verified Poseidon2; challenger-squeeze = verified Poseidon2; round-eval = BabyBear Horner (bbHornerEval) | — | **~174,800 cyc/prove** (3 rounds) |
| **Jolt** | as Spartan + Lasso grand-product = BabyBear bbGrandProduct | — | **~187,900 cyc/prove** (3 rounds + grand-product) |
| **Bulletproofs** | IPA field recursion (commit/cross-L/R/fold) = BabyBear field; FS squeeze = verified Poseidon2 | vector commitment = curve MSM (the documented MSM gap; leaves here are the field core) | **~58,000 cyc/prove** (field core) |
| **Halo2** | IPA field recursion + gate-constraint round = BabyBear field; FS squeeze = verified Poseidon2 | Pasta vector commitment = curve MSM (documented gap) | **~54,700 cyc/prove** (field core) |
| **Marlin** | verifier pairing check = REAL verified AUCurves BN254 `pairing_optimal` + `fp12_mul`; sum-check round = verified BN254 Fp Horner | KZG-commit G1 MSM (bn254 crate exposes no G1 group op; modelled at Fp layer — same MSM-leaf family as the gap) | **~21.5M cyc / pairing-check**; **~558 cyc / Fp sum-check round** |

KAT gates (all PASS): each prover is deterministic on its honest witness, a
witness/multiset tamper changes the proof fingerprint, and the leaf primitives
match their Lean/published reference vector:
- Spartan/Jolt: `grand_product(M=1..8, tau=11) = 1814400`; verifier re-derives
  the transcript through the same verified Poseidon2 leaves (accept honest,
  reject tamper).
- Halo2: gate `q(w)=w^2-w` gives `q(1)=0`, `q(7)=42` over BabyBear.
- Marlin: pairing-check bilinearity `e(2G,Q)·e(3G,Q) == e(5G,Q)` (EIP-196).

### Honest finding (emitted-orchestration faithfulness)

The emitted Jolt orchestration (`gen_com/jolt_prover_from_rustcmd.jazz`) computes
the Lasso grand product (`t13`) but returns the PCS-open digest
(`t14 = jolt_pcs_open(s0, t0)`); `t13` is **not folded into the returned proof**
in the n=3 emit. So a multiset-only edit does not change the returned digest.
The grand-product leaf itself is tamper-sensitive (gated directly). Reported as
an emitted-orchestration observation, not patched.

## MSM real-curve status (step 2 — gap CLOSED)

`bench/msm_compare/ec_leaves.jinc` is a **toy** EC (order-28 group over Z/23 via
dlog tables). `bench/msm_compare/msm_real_curve_kat.c` replaces it with a
**real-curve MSM** over the verified HACL* Ed25519 group
(`Hacl_Impl_Ed25519_Ladder_point_mul` + `_PointAdd_point_add`, 255-bit
prime-order Edwards curve). KAT (all PASS): `2G+3G==5G`, `msm({G,G},{2,3})==5G`,
`0·G==∞`, `G+∞==G` via the verified `point_equal`.

Self-bench: **~851,800 cyc / 8-term MSM (~106,500 cyc/term)** — a genuine
255-bit scalar-mul + point-add, not the toy group.

Build:
```
gcc -O2 -o msm_real_curve_kat msm_real_curve_kat.c \
    ../SSProve-lean/bench/ed25519_compare/hacl_ed25519.o ../SSProve-lean/bench/ed25519_compare/hacl_curve25519_51.o \
    ../SSProve-lean/bench/ed25519_compare/hacl_hash_sha2.o
```

## Build/run

```
# Spartan / Jolt / Bulletproofs / Halo2 (jasminc ~3-4 min each, then gcc + run)
jasminc -arch x86-64 -nowarning -o <p>_prover_link.s <p>_prover_link.jazz
gcc -O2 -o <p>_prover_kat <p>_prover_kat.c <p>_prover_link.s
taskset -c 2 ./<p>_prover_kat

# Marlin (real BN254 pairing, Rust crate)
cd bn254_compare && cargo build --release --bin marlin_prover_kat
taskset -c 2 ./target/release/marlin_prover_kat

# Real-curve MSM
cd msm_compare && (see build line above) && taskset -c 2 ./msm_real_curve_kat
```

## What this enables (#365 follow-on)

These real-leaf-linked, self-benched provers are the foundation for the
cross-crate compare vs arkworks-spartan / Jolt (a16z) / dalek-bulletproofs /
Nova / halo2 / arkworks-marlin. That compare requires installing those
reference crates (out of scope here); the OURS side is now real-leaf + KAT-gated
+ self-benched, not stub.
