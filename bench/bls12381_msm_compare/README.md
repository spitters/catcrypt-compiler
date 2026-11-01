# BLS12-381 G1 MSM against blst

Pippenger multi-scalar multiplication on BLS12-381 G1, composed from the emitted
field multiplication, the AUCurves safegcd inverse and Montgomery batch inversion,
compared with blst's `blst_p1s_mult_pippenger`. The `Makefile` header lists the targets.

Every target needs a sibling checkout of the CatCrypt development tree (not public):
blst, the field-multiplication assembly, the safegcd shim and the shared
measurement library are read from it. No default target or CI step of this repository
runs this harness.
