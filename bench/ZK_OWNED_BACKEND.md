# ZK provers through the OWNED x86 backend (#602)

Per-prover map of the hot field / MSM / pairing kernels each emitted ZK prover
spends its cycles in, and whether that kernel now routes through CatCrypt's
**owned x86 backend** (the in-Lean `*_x86_from_lean` leaves, no jasminc, no
external crate) versus the prior jasmin / external / stand-in path.

The trigger for this pass is that the BLS12-381 curve layer — the documented
"MSM / pairing residual" of every ZK prover in `ZK_CROSS_CRATE.md` /
`ZK_REAL_LEAF_BODIES.md` — is now owned-emitted:

| Owned BLS12-381 leg | What it is | KAT gate | bench dir |
|---|---|---|---|
| **#490** Fp Montgomery mul | in-Lean x86 CIOS multiply (`bls12381_mont_mul_x86_from_lean`) | == `blst_fp_mul` byte-for-byte | `bls12381_fieldmul_compare` |
| **#488** Fp inverse | AUCurves Bernstein-Yang safegcd divstep (`bls12_invert_divstep_sat`) | == `blst_fp_inverse` | `bls12381_safegcd_compare` |
| **#481** batch inversion | Montgomery's trick (1 inv + 3(n-1) mul) | == per-point inverse | `bls12381_msm_compare` |
| **#487** G1 MSM | composed Pippenger over the three legs above | == `blst_p1s_mult_pippenger` (n=256/1024/4096) | `bls12381_msm_compare` |
| **pp_map** (#602/#219) | owned Miller loop o final-exp (every Fp..Fp12 op an owned leaf) | == RELIC `pp_map_oatep` over random G1xG2 | `bls12381_ppmap_compare` |

## Per-prover hot-kernel routing

| Prover | hot kernel(s) | field core | curve MSM / pairing | owned-routable now? |
|---|---|---|---|---|
| **Groth16** | pairing-product verify `e(A,B)·∏e(Lᵢ,G2ᵢ)` | — (verify is pairing-only) | **3 pairings + 2 fp12_mul** | **YES — fully owned.** The owned `pp_map` IS the BLS12-381 pairing the verifier needs. Prior path: jasmin (`groth16_compare`, `jasminc -arch x86-64` over `bls_leaves.jinc`). |
| **Marlin** | KZG-commit G1 MSM + 2-pairing KZG verify + Fp sum-check | BN254 Fp Horner (jasmin) | BN254 pairing (jasmin/AUCurves); KZG G1 MSM modelled at Fp layer | **PARTIAL.** Owned BLS12-381 MSM + pp_map exist but Marlin is on **BN254**, not BLS12-381 — owned BN254 group/pairing is the gap. The owned BLS12-381 MSM is directly usable as the KZG-commit leaf *only if* Marlin is re-curved to BLS12-381 (ark-marlin's own curve). |
| **Bulletproofs** | Pedersen vector-commit MSM + IPA fold + Poseidon2 FS | BabyBear IPA (owned-emitted) | curve MSM = **Ed25519 stand-in** (HACL\* `point_mul`) | **MSM owned-routable** by swapping the Ed25519 stand-in for the owned BLS12-381 G1 MSM. (Protocol-exact group is Ristretto255; BLS12-381 is a different curve — see residual.) |
| **Halo2** | Pasta vector-commit MSM + gate + IPA fold + Poseidon2 FS | BabyBear IPA (owned-emitted) | curve MSM = **Ed25519 stand-in** (Pasta-exact was the #377 seam) | **MSM owned-routable** to the owned BLS12-381 G1 MSM as a real-curve cost (Pasta-exact owned group still absent — AUCurves Pasta point-add excluded from the dune build per `ZK_CROSS_CRATE.md` step 4). |
| **Spartan** | Hyrax commit MSM + IPA open + two-phase sum-check + Poseidon2 FS | BabyBear sum-check (owned-emitted) | curve MSM = Ed25519 stand-in | **MSM owned-routable** to owned BLS12-381 G1 MSM (protocol-exact group is curve25519/Ristretto — different curve). |
| **Jolt** | sum-check + Lasso grand-product + (PCS commit) | BabyBear field core (owned-emitted) | (PCS commit MSM, same family) | field core owned; **MSM owned-routable** as above. |
| **Plonky3** | FRI (Poseidon2 + NTT/LDE) — **hash-based, no curve** | BabyBear NTT/LDE + Poseidon2 (owned-emitted) | **no curve MSM / no pairing** | **N/A — Plonky3 is FRI/hash-based.** Its hot kernels (Poseidon2, NTT, Merkle) are already owned-emitted (`plonky3_compare`); the recursion wrapper is external. No BLS leaf applies. |
| **PLONK** | KZG-commit G1 MSM + pairing KZG verify | field core | (modelled) | **same as Marlin** — pairing-based; the owned BLS12-381 MSM + pp_map apply *if curved to BLS12-381*. |

## What this pass wired

The cleanest, no-curve-mismatch win is **Groth16**, because its verification
equation IS a BLS12-381 pairing product and the owned `pp_map` is exactly that
pairing. Wired into `bls12381_ppmap_compare/bls12381_ppmap_compare.c`:

- `owned_groth16_verify(A, B, L[], nL, G2)` — computes
  `e(A,B) == ∏ᵢ e(Lᵢ, G2)` as **3 owned `pp_map` + 2 owned `o_f12_mul`**, the
  same kernel structure the jasmin `groth16_compare` verifier emits, now routed
  through the owned x86 backend.
- `kat_groth16()` — gates it on the bilinearity witness
  `e(6·G1,G2) == e(1·G1,G2)·e(2·G1,G2)·e(3·G1,G2)` (= `e(G1,G2)^6`, since
  `1+2+3=6`) over the published BLS12-381 generators (RELIC `ep`/`ep2`
  generator multiples — no fabricated points), and verifies a tamper
  (`A=5·G1`) is **rejected**. Same anchor the jasmin `groth16_kat.rs` uses.
- `bench_owned_groth16(reps)` — times the owned verify (3 `pp_map` + 2 mul).

The KAT line is added to the gate and a Groth16-verify row to the microbench.

## Residual (precise, not faked)

- **Groth16: fully owned, no residual.** The verify pairing-product is exactly
  the owned `pp_map`; the only "external" pieces are RELIC for *generating* the
  witness generator-multiples (not in the timed kernel) and the canonical↔
  Montgomery bridging the owned tower-inverse carries (a modularity cost, the
  same one the standalone owned pp_map row already reports).
- **Marlin / PLONK: blocked on curve.** Owned MSM + pp_map are **BLS12-381**;
  these provers sit on **BN254** (Marlin's `bn254_compare`) / a modelled KZG
  curve. Re-curving them to BLS12-381 (ark-marlin's own curve) would make the
  owned BLS12-381 KZG-commit MSM + 2-pairing verify directly usable; that
  re-curve is the open item, not an owned-backend gap.
- **Bulletproofs / Halo2 / Spartan / Jolt: MSM owned-routable, but the
  protocol-exact group differs.** Their MSM is over Ristretto255 (Bulletproofs/
  Spartan), Pasta (Halo2), etc. The owned BLS12-381 G1 MSM gives a **real,
  verified-curve** MSM cost to replace the Ed25519 stand-in, but it is still a
  *stand-in group* for these protocols (a different 255/381-bit prime group),
  exactly as the Ed25519 stand-in was — the owned-emit improves *verified-ness*
  of the curve leaf, not protocol-exactness. The owned Pasta group remains
  absent (AUCurves Pasta point-add excluded from the dune build, per
  `ZK_CROSS_CRATE.md` §"Pasta-MSM status").
- **Plonky3: N/A** — FRI/hash-based, no curve kernel; already owned at the
  Poseidon2/NTT layer.

## Build / run (orchestrator)

```
# owned BLS12-381 pp_map + Groth16-verify routing (needs RELIC for witness gen)
make -C ../SSProve-lean/bench/bls12381_ppmap_compare emit      # re-emit owned fp_inv .s
make -C ../SSProve-lean/bench/bls12381_ppmap_compare kat        # gate: all tower layers + pp_map + GROTH16
make -C ../SSProve-lean/bench/bls12381_ppmap_compare run        # KAT + microbench (pp_map + groth16 verify)

# owned BLS12-381 G1 MSM vs blst (the curve-MSM leaf the IPA provers can adopt)
make -C bench/bls12381_msm_compare kat
make -C bench/bls12381_msm_compare run
```

The Groth16-verify row and its KAT are emitted by the `bls12381_ppmap_compare`
binary alongside the existing pp_map head-to-head; no new binary.
