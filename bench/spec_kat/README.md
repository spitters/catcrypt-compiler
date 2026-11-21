# Known-answer tests for the Lean specifications

`lake exe spec-kat --only <row>` checks the Lean specifications of SHAKE128, SHAKE256, SHA3-256,
BLAKE2s-256 and X25519 (the x-only ladder `xladderFold` driven by the RFC 7748 clamping, decoding
and inversion) against the vector files in `vectors/`, read at run time. The vectors are copies of
rows from the NIST CAVP SHA-3 byte-oriented files (`SHAKE128ShortMsg.rsp`, `SHAKE256ShortMsg.rsp`,
`SHA3_256ShortMsg.rsp`), RFC 7693 Appendix B and RFC 7748 Section 5.2; each file names its URL,
retrieval date and sha256. Run it from the workspace root with
`scripts/run-exe-rows.sh spec-kat --rows ../catcrypt-compiler/bench/spec_kat/rows.txt`
(the checkout of this repository as `bench/spec_kat/rows.txt` when it is the root); the exit code
is `1` when a vector differs.
