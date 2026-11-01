# BN254 MSM and EIP-197 pairing check

BN254 G1 MSM and EIP-197 pairing-verify kernels emitted from the front, checked
against the AUCurves reference. The `Makefile` header lists the targets.

The target that runs the `ec_pairing_owned_emit` driver reads it from a sibling
checkout of the CatCrypt development tree (not public) and fails without it; the other targets run Lean from this repository's root when that checkout is
absent. No default target or CI step of this repository runs this harness.
