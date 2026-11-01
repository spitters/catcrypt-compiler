# Pallas base-field Fp inversion bench (AUCurves BY/safegcd leaf).
#
# Adoption:
#   - The verified-front emit driver `pallas_emit.lean` writes
#     `gen_com/pallas_safegcd_invert_from_rustcmd.jazz` orchestrating
#     a single `pallas_invert_divstep_sat` extCall via the typed reg-ptr ABI.
#   - The leaf C symbol resolves at link time to the AUCurves Rust
#     staticlib built under `shim/` (a `#[no_mangle]` re-export of
#     `safegcd_pallas::pallas_invert_divstep_sat`).
#   - The KAT + bench harness wraps the leaf in a stable C signature
#     (`pallas_safegcd_invert`) and runs:
#       conform_pallas_safegcd: 4 KAT + 1000 random round-trips
#       bench_pallas_safegcd:   rdtsc median-of-3 cyc/op
#
# Trust profile: Coq kernel + AUCurves Bernstein-Yang divstep
# correctness (eprint 2019/266 + Pornin 2020 refinement) + AUCurves CI
# valgrind/crabgrind CT verification.
#
# Pipeline:
#   pallas_emit.lean
#       --(lake env lean ...)-->                gen_com/*.jazz
#   shim/Cargo.toml + shim/src/lib.rs
#       --(cargo build --release)-->            shim/target/release/libpallas_safegcd_shim.a
#   bench_pallas_safegcd.c
#       --(cc + tscbench + libshim.a)-->        ./bench_pallas_safegcd
#   conform_pallas_safegcd.c
#       --(cc + libshim.a)-->                   ./conform_pallas_safegcd

CC      ?= cc
CFLAGS  ?= -O3 -Wall -Wextra -march=native
REPS    ?= 100000

MEASLIB_DIR  := ../../../SSProve-lean/bench/measurement_lib
include $(MEASLIB_DIR)/Makefile.inc

JASMINC ?= $(HOME)/.opam/rocq-9/bin/jasminc
COMPILER := $(abspath $(CURDIR)/../..)
# Lake root: a sibling development checkout when present, this repository otherwise.
DEV      := $(or $(wildcard $(abspath $(COMPILER)/../SSProve-lean)),$(COMPILER))
# lake env/build from the dev root (one-root rule); the command runs in the compiler tree
LEAN_IN_COMPILER := cd $(DEV) && lake env sh -c 'cd $(COMPILER) && exec "$$@"' sh

# --- AUCurves staticlib (the BY/safegcd Pallas Fp leaf) ---
SHIM_DIR := shim
SHIM_LIB := $(SHIM_DIR)/target/release/libpallas_safegcd_shim.a

# AUCurves' build.rs compiles Jasmin / CryptOpt .asm to a sibling OUT_DIR
# of object files which the parent rlib references via `extern "C"`.
# Our staticlib only bundles the Rust bitcode, so we link those .o files
# alongside.  Use `wildcard` so this resolves to whatever the build.rs
# emitted on this machine.
SHIM_BUILD_OBJS := $(wildcard $(SHIM_DIR)/target/release/build/curve25519-jasmin-*/out/*.o)

.PHONY: all bench conform run emit shim clean

all: bench_pallas_safegcd conform_pallas_safegcd

$(MEASLIB_OBJS):
	$(MAKE) -C $(MEASLIB_DIR)

# Re-emit the .jazz from the verified front (optional; gen_com/*.jazz
# committed).
emit:
	$(LEAN_IN_COMPILER) lean bench/pallas_compare/pallas_emit.lean

# Build the AUCurves staticlib (re-exports pallas_invert_divstep_sat as
# C-linkable from the parent rlib).
shim: $(SHIM_LIB)

$(SHIM_LIB): $(SHIM_DIR)/Cargo.toml $(SHIM_DIR)/src/lib.rs
	cd $(SHIM_DIR) && JASMINC=$(JASMINC) cargo build --release

bench_pallas_safegcd: bench_pallas_safegcd.c pallas_safegcd_ref.h \
		$(SHIM_LIB) $(MEASLIB_OBJS)
	$(CC) $(CFLAGS) $(MEASLIB_CFLAGS) \
	    bench_pallas_safegcd.c $(MEASLIB_OBJS) $(SHIM_LIB) \
	    $(SHIM_BUILD_OBJS) \
	    -lpthread -ldl -lm \
	    -o $@

conform_pallas_safegcd: conform_pallas_safegcd.c pallas_safegcd_ref.h \
		$(SHIM_LIB)
	$(CC) $(CFLAGS) \
	    conform_pallas_safegcd.c $(SHIM_LIB) \
	    $(SHIM_BUILD_OBJS) \
	    -lpthread -ldl -lm \
	    -o $@

run: bench_pallas_safegcd conform_pallas_safegcd
	@echo "== conformance =="
	./conform_pallas_safegcd
	@echo
	@echo "== perf =="
	./bench_pallas_safegcd $(REPS)

clean:
	rm -f bench_pallas_safegcd conform_pallas_safegcd *.o
	cd $(SHIM_DIR) && cargo clean
