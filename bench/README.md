# Bench harnesses

The directories under `bench/` hold the emit drivers, known-answer tests and timing
harnesses of individual kernels. They are not part of the Lean package: no Lake target,
no CI step and no hook of this repository runs them, and each is invoked by hand with
`make` in its own directory.

A harness that runs Lean (`lake env`, `lake build`) runs it from this repository's root,
or from the root of a sibling checkout of the CatCrypt development tree when that
directory exists (the workspace in which this package was developed builds every package from one
root).

The following harnesses link objects, reference libraries or drivers of the CatCrypt
development tree, which is not public, and do not build without it. Each one's README
says which targets are affected.

| Directory | What needs the development tree |
| --- | --- |
| `bls12381_msm_compare` | every target: blst, the field-multiplication `.s`, the safegcd shim and the measurement library |
| `bn254_compare` | the `ec_pairing_owned_emit` driver target |
| `bn254_safegcd_compare` | every target: the shared measurement library |
| `pallas_compare` | every target: the shared measurement library |
| `msm_compare` | the real-curve and Straus KATs, which link HACL\* objects |
| `plonky3_compare` | the `catcrypt-plonky3` crate targets, the butterfly emit drivers and the Poseidon2 leaves |
| `p384_ecdsa_rust` | the default s2n-bignum checkout (`S2N_BIGNUM_DIR` overrides it) |
| `s2n_import` | the default s2n-bignum checkout and owned assembly (`S2N_BIGNUM_DIR`, `OWNED_ASM` override them) |
