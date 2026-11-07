# The region-compiled template kernels SHA-512 compression, BLAKE2b compression and
# Keccak-f[1600] (ELF objects in gen/, written by `lake exe linked-kernel-emit`) against
# OpenSSL, HACL* and XKCP. README.md states the arms, the adapters and the method.
#
# Run every target except `gen` through the heavy-run wrapper from the repository root:
#   make -C bench/hash_linked_compare gen                                      # emit gen/*.o (Lean)
#   bash scripts/heavy-run.sh make -C bench/hash_linked_compare                # build
#   bash scripts/heavy-run.sh make -C bench/hash_linked_compare conform        # vectors + random batch
#   bash scripts/heavy-run.sh make -C bench/hash_linked_compare run LABEL="..."  # conform, then timing runs
#   bash scripts/heavy-run.sh make -C bench/hash_linked_compare disasm         # instruction census
#   make -C bench/hash_linked_compare provenance                               # hashes and versions
#
# `gen` is not run under heavy-run.sh: scripts/run-exe-rows.sh routes each row through
# heavy-run.sh itself.

CC        ?= cc
OBJDUMP   ?= objdump
OPTFLAGS  ?= -O3 -march=native
WARNFLAGS ?= -Wall -Wextra
LDFLAGS   ?= -Wl,-z,noexecstack

CPU      ?= 2
LABEL    ?= unlabelled
SAMPLES  ?= 501
INNER    ?= 500
NRAND    ?= 10000
RUNS     ?= 1 2 3

COMPILER := $(abspath $(CURDIR)/../..)
# Lake root and the scripts heavy-run.sh and run-exe-rows.sh: the sibling development
# checkout (one build root). The executable writes its objects relative to the directory it
# runs in; `gen` copies them here.
DEV      := $(abspath $(COMPILER)/../SSProve-lean)

# Peers, by default checkouts beside this package; set LIBCRUX and XKCP_DIR to override.
LIBCRUX  ?= $(abspath $(COMPILER)/../libcrux)
HACL_SRC := $(LIBCRUX)/sys/hacl/c/src
HACL_INC := $(LIBCRUX)/sys/hacl/c/include
HACL_INT := $(LIBCRUX)/sys/hacl/c/include/internal
HACL_KRM := $(LIBCRUX)/sys/hacl/c/karamel/include
HACL_K2  := $(LIBCRUX)/sys/hacl/c/karamel/krmllib/dist/minimal
HACL_CFLAGS := -I$(HACL_SRC) -I$(HACL_INC) -I$(HACL_INT) -I$(HACL_KRM) -I$(HACL_K2)
# XKCP KeccakP-1600 opt64, as vendored by the FAEST reference implementation.
XKCP_DIR ?= $(abspath $(COMPILER)/../faest-ref-v3/sha3)
XKCP_CFLAGS := -I$(XKCP_DIR)/opt64 -I$(XKCP_DIR)
OPENSSL_LIBS ?= -lcrypto

MEASLIB_DIR := $(DEV)/bench/measurement_lib
include $(MEASLIB_DIR)/Makefile.inc

# Our objects: written by the rows sha512_compress, blake2b_compress, keccak_f1600 of the
# executable below (repository paths bench/hash_linked_compare/gen/sha512_compress.o,
# bench/hash_linked_compare/gen/blake2b_compress.o, bench/hash_linked_compare/gen/keccak_f1600.o).
OURS := gen/sha512_compress.o gen/blake2b_compress.o gen/keccak_f1600.o

EMIT_EXE    := linked-kernel-emit
EMIT_MODULE := CatCrypt.Crypto.SecureCompilation.HashTemplate.LinkedKernelEmitMain
EMIT_SRC    := $(COMPILER)/CatCrypt/Crypto/SecureCompilation/HashTemplate/LinkedKernelEmitMain.lean
EMIT_DEPS   := $(EMIT_SRC) \
  $(COMPILER)/CatCrypt/Crypto/SecureCompilation/HashTemplate/Sha2Linked.lean \
  $(COMPILER)/CatCrypt/Crypto/SecureCompilation/HashTemplate/Blake2Linked.lean \
  $(COMPILER)/CatCrypt/Crypto/SecureCompilation/HashTemplate/KeccakLinked.lean

BUILD := build

.PHONY: all gen conform run disasm provenance clean

all: $(BUILD)/compare

$(BUILD):
	mkdir -p $(BUILD) results

$(MEASLIB_OBJS):
	$(MAKE) -C $(MEASLIB_DIR)

# Writes gen/<row>.o for the three hash rows of $(EMIT_EXE) (root $(EMIT_MODULE)); each
# row runs under its budget in bench/exe_budget.tsv and is recorded in
# bench/exe_budget_runs.tsv.
gen: $(EMIT_DEPS)
	mkdir -p gen
	cd $(DEV) && bash scripts/heavy-run.sh lake build $(EMIT_EXE)
	$(COMPILER)/.lake/build/bin/$(EMIT_EXE) --list > $(CURDIR)/gen/rows.txt
	cd $(DEV) && bash scripts/run-exe-rows.sh $(EMIT_EXE) --no-build --rows $(CURDIR)/gen/rows.txt
	cp $(DEV)/bench/hash_linked_compare/gen/*.o gen/

# Peer and adapter objects at -O3 -march=native (the peers' best portable build here).
$(BUILD)/refs.o: refs.c arms.h | $(BUILD)
	$(CC) $(OPTFLAGS) -w $(HACL_CFLAGS) $(XKCP_CFLAGS) -c $< -o $@
$(BUILD)/hacl_sha2.o: $(HACL_SRC)/Hacl_Hash_SHA2.c | $(BUILD)
	$(CC) $(OPTFLAGS) -w $(HACL_CFLAGS) -c $< -o $@
$(BUILD)/hacl_sha3.o: $(HACL_SRC)/Hacl_Hash_SHA3.c | $(BUILD)
	$(CC) $(OPTFLAGS) -w $(HACL_CFLAGS) -c $< -o $@
$(BUILD)/lib_memzero0.o: $(HACL_SRC)/Lib_Memzero0.c | $(BUILD)
	$(CC) $(OPTFLAGS) -w $(HACL_CFLAGS) -c $< -o $@
$(BUILD)/xkcp_opt64.o: $(XKCP_DIR)/opt64/KeccakP-1600-opt64.c | $(BUILD)
	$(CC) $(OPTFLAGS) -w $(XKCP_CFLAGS) -c $< -o $@
$(BUILD)/tramp.o: tramp.c | $(BUILD)
	$(CC) -O2 $(WARNFLAGS) -c $< -o $@

PEER_OBJS := $(BUILD)/refs.o $(BUILD)/hacl_sha2.o $(BUILD)/hacl_sha3.o \
  $(BUILD)/lib_memzero0.o $(BUILD)/xkcp_opt64.o

$(BUILD)/compare: compare.c arms.h $(OURS) $(BUILD)/tramp.o $(PEER_OBJS) $(MEASLIB_OBJS) | $(BUILD)
	$(CC) $(OPTFLAGS) $(WARNFLAGS) $(MEASLIB_CFLAGS) compare.c $(BUILD)/tramp.o $(OURS) \
	  $(PEER_OBJS) $(MEASLIB_OBJS) $(OPENSSL_LIBS) $(LDFLAGS) -o $@

conform: $(BUILD)/compare
	./$(BUILD)/compare conform $(NRAND) | tee results/conform.txt

# Conformance gates the timing: a failing arm stops the run.
run: conform
	@for k in $(RUNS); do \
	  taskset -c $(CPU) ./$(BUILD)/compare bench --cpu $(CPU) --samples $(SAMPLES) \
	    --inner $(INNER) --run $$k --label "$(LABEL)" > results/run$$k.tsv || exit 1; \
	  cat results/run$$k.tsv; \
	done

# Per object: .text bytes, instruction count, memory operands, stack operands, branches.
disasm: $(OURS)
	@printf '%-28s %6s %6s %6s %6s  %s\n' function bytes insns memops stack branches/calls
	@for o in $(OURS); do \
	  sym=catcrypt_$$(basename $$o .o); \
	  $(OBJDUMP) -d --disassemble=$$sym $$o | awk -F'\t' -v sym=$$sym ' \
	    NF >= 2 && $$1 ~ /:$$/ { nb += split($$2, b, " "); if (NF < 3) next; \
	      split($$3, w, " "); m = w[1]; t++; \
	      if ($$3 ~ /\(/ && m !~ /^lea/) mem++; if ($$3 ~ /\(%rsp\)/) stk++; \
	      if (m ~ /^j/ || m ~ /^call/ || m ~ /^loop/) br = br " " m; } \
	    END { printf "%-28s %6d %6d %6d %6d  %s\n", sym, nb, t, mem, stk, (br == "" ? "none" : br) }'; \
	done

provenance:
	@echo "OpenSSL: $$(openssl version)"
	@echo "HACL*: libcrux $$(git -C $(LIBCRUX) rev-parse HEAD 2>/dev/null) (sys/hacl/c)"
	@echo "XKCP: faest-ref $$(git -C $(XKCP_DIR)/.. rev-parse HEAD 2>/dev/null) (sha3/opt64)"
	@md5sum $(OURS)
	@stat -c '%y  %n' $(OURS)

clean:
	rm -rf $(BUILD)
