# Import s2n-bignum's bignum_montmul_p384 and bignum_montsqr_p384 into
# CatCrypt's JInstr 64 IR, print them back with CatCrypt's x86 printer, encode
# them with CatCrypt's byte encoder, and check the results against s2n-bignum.
#
#   make import    # regenerate both Lean modules from the s2n-bignum sources
#   make reemit    # print gen/<kernel>_reemitted.s from the modules
#   make encode    # write gen/<kernel>_encoded.s through the encoder
#   make compare   # instruction counts, sizes and differences against the archive
#   make field     # known-answer gate and timing, in ../p384_ecdsa_rust
#   make framed-kat  # encode the framed montmul, test it against s2n-bignum
#   make import-owned   # import the owned backend's shipped Ed25519 functions
#   make compare-owned  # print them back and compare with their sources
#
# Per kernel: import-montmul, import-montsqr, reemit-montmul, reemit-montsqr,
# encode-montmul, encode-montsqr, compare-montmul, compare-montsqr.
#
# `reemit`, `encode` and `encode-framed` run `lake lean` from the repository
# root, which builds the Lean modules if needed. `field` needs all four
# generated files, and `framed-kat` needs gen/bignum_montmul_p384_framed.s.
#
# Variables:
#   S2N_BIGNUM_DIR  the s2n-bignum checkout; the archive is
#                   $(S2N_BIGNUM_DIR)/x86/libs2nbignum.a. Default: the checkout
#                   in the sibling SSProve-lean tree.
#   OWNED_ASM       the directory of the shipped owned-backend files named in
#                   owned_kernels.txt. Default: crates/catcrypt-ed25519/asm in
#                   the sibling SSProve-lean tree.
#   HEAVY_RUN       a wrapper for the `lake lean` commands. Default: the
#                   sibling SSProve-lean tree's scripts/heavy-run.sh when that
#                   file exists, otherwise none.

REPO := $(abspath ../..)
S2N_BIGNUM_DIR ?= $(abspath $(REPO)/../SSProve-lean/bench/reference_install/s2n-bignum)
export S2N_BIGNUM_DIR
HEAVY_RUN ?= $(wildcard $(abspath $(REPO)/../SSProve-lean/scripts/heavy-run.sh))
DEMOS := $(REPO)/CatCrypt/Crypto/SecureCompilation/Ascent/Demos
LEAN_MODULE := $(DEMOS)/S2nMontmulP384.lean
BYTES_MODULE := $(DEMOS)/S2nMontmulP384Bytes.lean
SQR_MODULE := $(DEMOS)/S2nMontsqrP384.lean
REEMITTED := gen/bignum_montmul_p384_reemitted.s
ENCODED := gen/bignum_montmul_p384_encoded.s
SQR_REEMITTED := gen/bignum_montsqr_p384_reemitted.s
SQR_ENCODED := gen/bignum_montsqr_p384_encoded.s
FRAMED_MODULE := $(DEMOS)/S2nMontmulP384Framed.lean
FRAMED := gen/bignum_montmul_p384_framed.s
S2N_LIB := $(S2N_BIGNUM_DIR)/x86/libs2nbignum.a
IMPORTER := import_s2n.sh translate.awk
LAKE_LEAN := cd $(REPO) && LEAN_NUM_THREADS=1 $(if $(HEAVY_RUN),bash $(HEAVY_RUN)) lake lean

.PHONY: import import-montmul import-montsqr reemit reemit-montmul reemit-montsqr \
        encode encode-montmul encode-montsqr compare compare-montmul compare-montsqr field \
        encode-framed framed-kat import-owned reemit-owned compare-owned

import: import-montmul import-montsqr

import-montmul:
	./import_s2n.sh bignum_montmul_p384

import-montsqr:
	./import_s2n.sh bignum_montsqr_p384

reemit: reemit-montmul reemit-montsqr
reemit-montmul: $(REEMITTED)
reemit-montsqr: $(SQR_REEMITTED)

$(REEMITTED): $(LEAN_MODULE) reemit.lean
	$(LAKE_LEAN) bench/s2n_import/reemit.lean

$(SQR_REEMITTED): $(SQR_MODULE) reemit_montsqr.lean
	$(LAKE_LEAN) bench/s2n_import/reemit_montsqr.lean

encode: encode-montmul encode-montsqr
encode-montmul: $(ENCODED)
encode-montsqr: $(SQR_ENCODED)

$(ENCODED): $(LEAN_MODULE) $(BYTES_MODULE) encode.lean
	$(LAKE_LEAN) bench/s2n_import/encode.lean

$(SQR_ENCODED): $(SQR_MODULE) encode_montsqr.lean
	$(LAKE_LEAN) bench/s2n_import/encode_montsqr.lean

compare: compare-montmul compare-montsqr

compare-montmul: $(REEMITTED) $(ENCODED)
	./compare_insns.sh bignum_montmul_p384

compare-montsqr: $(SQR_REEMITTED) $(SQR_ENCODED)
	./compare_insns.sh bignum_montsqr_p384

encode-framed: $(FRAMED)

$(FRAMED): $(FRAMED_MODULE) encode_framed.lean
	$(LAKE_LEAN) bench/s2n_import/encode_framed.lean

# Random, in-place and squaring vectors against bignum_montmul_p384, and the
# six callee-saved registers across a call.
framed-kat: $(FRAMED) kat_framed/kat.c kat_framed/check_saved.s
	@test -f $(S2N_LIB) || { echo "framed-kat: no $(S2N_LIB); set S2N_BIGNUM_DIR to a built s2n-bignum checkout" >&2; exit 2; }
	gcc -O2 -o gen/framed_kat kat_framed/kat.c kat_framed/check_saved.s $(FRAMED) $(S2N_LIB)
	./gen/framed_kat

field: $(REEMITTED) $(ENCODED) $(SQR_REEMITTED) $(SQR_ENCODED)
	$(MAKE) -C ../p384_ecdsa_rust field-asm

# The owned backend's shipped functions (owned_kernels.txt): import them,
# print them back with reemit_owned.lean, compare with the sources.
OWNED_ASM ?= $(abspath $(REPO)/../SSProve-lean/crates/catcrypt-ed25519/asm)
IMPORTED := $(REPO)/CatCrypt/Crypto/SecureCompilation/Ascent/Imported
OWNED_MODULES := $(shell awk 'NF == 3 && substr($$1, 1, 1) != "\043" { print $$1 }' owned_kernels.txt)
OWNED_STAMP := gen/owned/.reemitted

import-owned:
	awk 'NF == 3 && substr($$1, 1, 1) != "\043"' owned_kernels.txt | while read -r m f s; do \
	  ./import_owned.sh "$(OWNED_ASM)/$$f" "$$m" "$$s" || exit 1; done

reemit-owned: $(OWNED_STAMP)

$(OWNED_STAMP): $(OWNED_MODULES:%=$(IMPORTED)/%.lean) $(IMPORTED)/CallSeg.lean reemit_owned.lean
	$(LAKE_LEAN) bench/s2n_import/reemit_owned.lean
	touch $@

compare-owned: $(OWNED_STAMP)
	OWNED_ASM="$(OWNED_ASM)" ./compare_owned.sh
