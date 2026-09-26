# CONN-3e (#331): the BN254 G1 affine point-add re-emitted as a COMPOSITION over
# the AUCurves verified FIELD leaves (Pairing/BN254GroupEmit.lean), KAT'd
# byte-identical against the published BN254 generator-multiple spec vectors.
#
#   Pairing/Bn254Emit.lean       emits `bn254_g1_add` as ONE opaque group leaf.
#   Pairing/BN254GroupEmit.lean  re-emits the same group op as a straight-line
#     `Com` over the field leaves fp_mul / fp_sub / fp_inv, and proves
#     (emittedAffineAdd_realizes) the Com denotation equals bn254AffineAdd
#     over FpBN254 (Util/BN254Verified.lean).
#
# This KAT confirms the re-emitted field-leaf composition computes the SAME
# bytes as the published BN254 spec multiples: only the emit granularity changed.
#
#   - Composition: the lambda / Rx / Ry chain on the AUCurves verified field
#     leaves (bn254-safe-rust: fp_sub/fp_mul + Fermat fp_inv).
#   - Reference: the published BN254 (alt_bn128) generator multiples
#     G1, 2G1, 3G1, 5G1 (no fabricated vectors); byte-identity on the canonical
#     32-byte little-endian Montgomery-limb encoding.
#
# Targets:
#   make kat    # build + run the byte-identity KAT

.PHONY: kat clean

kat:
	cargo build --release
	./target/release/bn254_group_kat

clean:
	cargo clean
