# Whole hash functions: the compiler's entries sha3_256_words, shake128_256_words,
# shake256_512_words (sponge-hax), blake2b_512_words (blake2b-hax) and sha512_words
# (sha512-hax), compiled by compileA with the region-compiled compression or permutation
# linked (ELF objects in gen/), against HACL* full hashes, OpenSSL EVP and libsodium
# crypto_generichash. README.md states the arms and the interface.
#
#   make kat                   build `whole` and run the known-answer checks
#   make bench-build           build `whole-bench` (timing; run it on the reference host)
#   make run LABEL="..."       known-answer checks, then timing runs (reference host)
#
# The arms are built in when their parts exist: HACL* when $(HACL_SRC) has the sources
# (HACL=0 to leave it out), ours when gen/ has the five objects (OURS=0 to leave them out).

CC        ?= cc
OPTFLAGS  ?= -O3 -march=native
WARNFLAGS ?= -Wall -Wextra
LDFLAGS   ?= -Wl,-z,noexecstack

CPU      ?= 2
LABEL    ?= unlabelled
SAMPLES  ?= 101
INNER    ?= 50
RUNS     ?= 1 2 3

COMPILER := $(abspath $(CURDIR)/../..)
DEV      ?= $(abspath $(COMPILER)/../SSProve-lean)

LIBCRUX  ?= $(HOME)/Claude/libcrux
HACL_SRC := $(LIBCRUX)/sys/hacl/c/src
HACL_CFLAGS := -I$(HACL_SRC) -I$(LIBCRUX)/sys/hacl/c/include \
  -I$(LIBCRUX)/sys/hacl/c/include/internal -I$(LIBCRUX)/sys/hacl/c/karamel/include \
  -I$(LIBCRUX)/sys/hacl/c/karamel/krmllib/dist/minimal
HACL ?= $(if $(wildcard $(HACL_SRC)/Hacl_Hash_SHA2.c),1,0)

OPENSSL_LIBS ?= -lcrypto
# libsodium: pkg-config when the development files are installed, otherwise the runtime
# library by its soname (whole.c declares the two functions it calls).
SODIUM_LIBS ?= $(shell pkg-config --libs libsodium 2>/dev/null || echo -l:libsodium.so.23)

# Our objects, symbol catcrypt_<entry>.
OURS_OBJS := gen/sha3_256_words.o gen/shake128_256_words.o gen/shake256_512_words.o \
  gen/blake2b_512_words.o gen/sha512_words.o
OURS ?= $(if $(strip $(foreach o,$(OURS_OBJS),$(if $(wildcard $(o)),,missing))),0,1)

BUILD := build
DEFS :=
OBJS :=
ifeq ($(HACL),1)
DEFS += -DWITH_HACL
OBJS += $(BUILD)/peers_hacl.o $(BUILD)/hacl_sha2.o $(BUILD)/hacl_sha3.o \
  $(BUILD)/hacl_blake2b.o $(BUILD)/lib_memzero0.o
endif
ifeq ($(OURS),1)
DEFS += -DWITH_OURS
OBJS += $(OURS_OBJS)
endif

.PHONY: kat bench-build run clean

kat: $(BUILD)/whole
	./$(BUILD)/whole kat | tee results/kat.txt

$(BUILD):
	mkdir -p $(BUILD) results

$(BUILD)/peers_hacl.o: peers_hacl.c | $(BUILD)
	$(CC) $(OPTFLAGS) -w $(HACL_CFLAGS) -c $< -o $@
$(BUILD)/hacl_sha2.o: $(HACL_SRC)/Hacl_Hash_SHA2.c | $(BUILD)
	$(CC) $(OPTFLAGS) -w $(HACL_CFLAGS) -c $< -o $@
$(BUILD)/hacl_sha3.o: $(HACL_SRC)/Hacl_Hash_SHA3.c | $(BUILD)
	$(CC) $(OPTFLAGS) -w $(HACL_CFLAGS) -c $< -o $@
$(BUILD)/hacl_blake2b.o: $(HACL_SRC)/Hacl_Hash_Blake2b.c | $(BUILD)
	$(CC) $(OPTFLAGS) -w $(HACL_CFLAGS) -c $< -o $@
$(BUILD)/lib_memzero0.o: $(HACL_SRC)/Lib_Memzero0.c | $(BUILD)
	$(CC) $(OPTFLAGS) -w $(HACL_CFLAGS) -c $< -o $@

$(BUILD)/whole: whole.c kat_table.h Makefile $(OBJS) | $(BUILD)
	$(CC) $(OPTFLAGS) $(WARNFLAGS) $(DEFS) whole.c $(OBJS) $(OPENSSL_LIBS) $(SODIUM_LIBS) \
	  $(LDFLAGS) -o $@

MEASLIB_DIR := $(DEV)/bench/measurement_lib
# The measurement library of the development checkout, needed only by whole-bench.
-include $(MEASLIB_DIR)/Makefile.inc

$(MEASLIB_OBJS):
	$(MAKE) -C $(MEASLIB_DIR)

$(BUILD)/whole-bench: whole.c kat_table.h Makefile $(OBJS) $(MEASLIB_OBJS) | $(BUILD)
	$(CC) $(OPTFLAGS) $(WARNFLAGS) $(DEFS) -DWITH_BENCH $(MEASLIB_CFLAGS) whole.c $(OBJS) \
	  $(MEASLIB_OBJS) $(OPENSSL_LIBS) $(SODIUM_LIBS) $(LDFLAGS) -o $@

bench-build: $(BUILD)/whole-bench

# The known-answer checks gate the timing: a failing arm stops the run.
run: $(BUILD)/whole-bench
	@for k in $(RUNS); do \
	  taskset -c $(CPU) ./$(BUILD)/whole-bench bench --cpu $(CPU) --samples $(SAMPLES) \
	    --inner $(INNER) --run $$k --label "$(LABEL)" > results/run$$k.tsv || exit 1; \
	  cat results/run$$k.tsv; \
	done

clean:
	rm -rf $(BUILD)
