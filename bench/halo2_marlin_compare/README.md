# Halo2 / Marlin (ZK Tier 3) — Axis-A bench status

This is the Tier-3 entry of the ZK-honesty sweep (Plonky3 → STARK → Spartan/Jolt
→ Bulletproofs/IVC → **Halo2/Marlin**). Tier 3's hot primitives are the
**polynomial-commitment commitment + opening check**:

* **Halo2** uses **IPA over the Pasta cycle** (no trusted setup) — its hot
  primitive is the EC point-add / scalar-multiply MSM, the *same* emitted leaf
  the Tier-2 Bulletproofs/IVC realization reuses.
* **Marlin** uses **KZG over a pairing group** (universal/updatable SRS) — its
  hot primitive is the bilinear pairing check `e(·,·) : G1 × G2 → GT = Fp12`,
  computed by a Miller loop + final exponentiation over the Fp12 tower.

Per the Tier-2 discipline (which reused `bench/msm_compare` for the MSM leaf and
deferred the full `dalek-bulletproofs`/Nova end-to-end bench since those
references are not installed), Tier 3 reuses the **already-emitted, KAT-gated**
commitment leaves rather than duplicating them. The full `halo2` (zcash) /
`arkworks-marlin` end-to-end prover benches are deferred — those crates are not
in the reference installation of the CatCrypt development tree (not public).

## The emitted, KAT-gated Tier-3 commitment leaves (Axis A)

| Protocol | Commitment scheme | Emitted + KAT-gated leaf | Reference |
|---|---|---|---|
| Halo2 | IPA / Pasta MSM | `bench/msm_compare` (`make kat`, 7/7 cases byte-identical) | schoolbook EC reference |
| Marlin | KZG pairing check | `kzg_compare` bench of the CatCrypt development tree (not public; `make kat`) — emitted Fp12 `e(·,·)` opening verifier | AUCurves verified reference, BLS12-381 generators |
| Marlin | KZG base field / Fp2 tower | `bench/bn254_compare` (BN254 field + Fp2 KAT) | AUCurves jasmin tower |

`make kat` in that `kzg_compare` bench confirms the emitted KZG opening verifier agrees
with the AUCurves verified reference:

```
ok:   kzg verify  e(pi, [s-z]G2) == e(C-[y]G1, G2)
ok:   kzg verified value e(G1,G2)^6 is non-trivial in GT (not the identity)
KAT PASSED (emitted KZG opening verifier agrees with the AUCurves verified reference;
            pairing values anchored to the published BLS12-381 generators)
```

`make kat` in `bench/msm_compare` confirms the emitted MSM leaf (Halo2's IPA hot
primitive) is byte-identical to the EC reference over its 7 cases.

## Axis B — security connection (the Tier-3 deliverable)

The Axis-B ties live in Lean modules of the CatCrypt development tree (not public):

* `CatCrypt.Crypto.ZK.Halo2EmittedIPARealization` —
  `halo2_group_layer_connected`: the emitted MSM/EC point-add / scalar-multiply
  leaves realize the Pasta-cycle commitment ops the Halo2 IPA soundness theorem
  quantifies over (CONN-3 `EcLeafAgrees` / `msm_eq_scalarFold`); the composed
  witness-using `halo2IPAProver` retires `trivialUniformHalo2Prover` for the
  soundness-connected statement (`halo2_msm_connected_uc_zero`). Named residual:
  `Halo2_IPA_KnowledgeSoundness_at` (DLOG on Pasta, input pinned to the emitted
  `ec_scalar_mul` leaf).
* `CatCrypt.Crypto.ZK.Marlin.EmittedKZGRealization` —
  `marlin_pairing_layer_connected`: the emitted Fp12 (GT) pairing-tower mul/add
  leaves are the arithmetic the KZG pairing check is built from, round-tripping
  through the verified compiler (`fp6Fp12Tower_roundtrip`); the composed
  witness-using `marlinKZGProver` retires `trivialUniformMarlinProver` for the
  soundness-connected statement (`marlin_kzg_connected_uc_zero`). Named residual:
  `Marlin_KZG_Binding_at` (q-SDH/AGM in the pairing group, input pinned to the
  emitted Fp12 tower).

Both headline theorems are axiom-clean (`propext` / `Classical.choice` /
`Quot.sound`); the Marlin pairing-layer connection additionally inherits the
pre-existing `native_decide` round-trip axioms of `fp6Fp12Tower_roundtrip` (the same tier as the other
emitted-leaf realizations), introducing no new content of its own.
