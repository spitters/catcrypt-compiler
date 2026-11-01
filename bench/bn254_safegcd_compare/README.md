# BN254 field inversion (safegcd)

Timing of the AUCurves Bernstein-Yang inverter for the BN254 base field, called
through the staticlib shim in `shim/`. The `Makefile` header lists the targets.

The `Makefile` includes the shared measurement library of a sibling checkout of the
CatCrypt development tree (not public), so no target builds without it. No default target or CI step of this repository runs this harness.
