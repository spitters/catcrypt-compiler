# Multi-scalar multiplication

The MSM kernel emitted from the front, checked byte for byte against the schoolbook
reference `ec_ref.h`. The `Makefile` header lists the targets.

The emit and KAT targets run Lean from this repository's root when no development
checkout is present. The real-curve KAT `msm_real_curve_kat.c` and the Straus driver
`msm_straus.c` link HACL\* objects built in a sibling checkout of the CatCrypt
development tree (not public). No default target or CI step of this
repository runs this harness.
