# BN254 (alt_bn128) Fp BY/safegcd inversion bench (AUCurves safegcd_bn254).
#
# Headline: AUCurves' verified-CT Bernstein-Yang divstep inverter
#   ~/Claude/BLS/AUCurves/curve25519-jasmin-rs/src/safegcd_bn254.rs
#   (bn254_invert_divstep_sat), re-exported via the staticlib shim in
#   shim/ under the C symbol `safegcd_bn254_invert`.
#
# Trust = Coq/Rocq kernel + AUCurves' divstep convergence certificate +
#   the in-tree schoolbook x·x^-1≡1 KAT (safegcd_bn254.rs::tests).
#
# #489: BN254 was the one production curve whose Fp inverse was still the
# Fermat a^(p-2) chain; the cross-curve audit flipped it onto this divstep
# leaf, matching the BLS12-381 / P-256 / secp256k1 recipe.
#
# The verified-front Lean wiring is in bn254_safegcd_emit.lean (mirrors
# p256_safegcd_emit.lean): the front emits a single-RCall .jazz around
# the leaf symbol `safegcd_bn254_invert`.  This bench exercises the leaf
# directly (the emit produces the .jazz orchestration; the leaf is the
# linked AUCurves-verified Rust body).
#
# KAT before measuring: x · BY^-1(x) ≡ 1 (mod p_BN254) for AUCurves' own
# deterministic inputs (incl. p-1), via a schoolbook mul-mod reference —
# the same x·x^-1≡1 identity AUCurves' own tests check.  Bench aborts on
# KAT failure.
#
# Targets:
#   make emit     # (re)emit gen_com/*.jazz from Lean (verified-front witness)
#   make bench    # build the bench harness (KAT-gated)
#   make run      # run the bench
#   make shim     # build the AUCurves staticlib shim
#   make clean

CC      ?= cc
CARGO   ?= cargo
CFLAGS  ?= -O3 -Wall -Wextra -march=native
REPS    ?= 5000
COMPILER := $(abspath $(CURDIR)/../..)
DEV      := $(abspath $(COMPILER)/../SSProve-lean)
# lake env/build from the dev root (one-root rule); the command runs in the compiler tree
LEAN_IN_COMPILER := cd $(DEV) && lake env sh -c 'cd $(COMPILER) && exec "$$@"' sh

MEASLIB_DIR  := ../../../SSProve-lean/bench/measurement_lib
include $(MEASLIB_DIR)/Makefile.inc

SHIM_DIR     := shim
SHIM_TARGET  := $(SHIM_DIR)/target/release
SHIM_LIB     := $(SHIM_TARGET)/libbn254_safegcd_shim.a

.PHONY: all emit bench run clean shim

all: bench

emit:
	$(LEAN_IN_COMPILER) lean bench/bn254_safegcd_compare/bn254_safegcd_emit.lean

$(MEASLIB_OBJS):
	$(MAKE) -C $(MEASLIB_DIR)

shim: $(SHIM_LIB)

$(SHIM_LIB): $(SHIM_DIR)/src/lib.rs $(SHIM_DIR)/Cargo.toml
	cd $(SHIM_DIR) && $(CARGO) build --release

bench_bn254_safegcd: bench_bn254_safegcd.c bn254_safegcd_ref.h $(SHIM_LIB) $(MEASLIB_OBJS)
	$(CC) $(CFLAGS) $(MEASLIB_CFLAGS) \
	    bench_bn254_safegcd.c \
	    $(MEASLIB_OBJS) \
	    $(SHIM_LIB) \
	    -lpthread -ldl -lm -lgmp \
	    -o bench_bn254_safegcd

bench: bench_bn254_safegcd

run: bench_bn254_safegcd
	@echo "== safegcd_bn254 BY-inversion bench =="
	taskset -c 3 ./bench_bn254_safegcd $(REPS)

clean:
	rm -f bench_bn254_safegcd *.o
	cd $(SHIM_DIR) && $(CARGO) clean
