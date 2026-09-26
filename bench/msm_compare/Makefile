# Multi-scalar-multiplication (MSM) kernel emitted from CatCrypt's verified front,
# KAT'd byte-identical vs the independent schoolbook EC reference (ec_ref.h).
#
# MSM  Sum_{i=0}^{L-1} k_i * P_i  over an EC group is the prover/commitment hot
# computation shared by Groth16, KZG, and Bulletproofs.  It is the committed
# `scalarFold` reduction at the EC-group lane (lane op = scalar*point, hsum =
# point-add): MsmReduce.msm_eq_scalarFold / MsmEmit.msmKernel_dot.
#
# Pipeline (OWNED x86-64, no jasminc):
#   msm_owned_emit.lean --(lake env lean --run)-->            gen_com/msm.s
#       (whole ec_msm: prologue + LprogControlFlow.loopLcmd bounded `for i=0..8`
#        loop + epilogue, rendered by LprogAsmPrinter.renderLfundef)
#   gen_com/msm.s + msm_kat.c (builds DLOG/POW tables + links ec_ref.h oracle)
#                   --(gcc)-->                                     ./msm_kat
#
# The Z/23 EC group law runs in DLOG space inside the owned kernel: point-add is
# (i+j) mod 28, scalar-mul is (k*j) mod 28 (Barrett), no modular inverse. The
# DLOG[23*x+y] / POW[m] leaf tables are u64-per-entry and passed IN by msm_kat.c,
# built there from ec_ref.h's OWN group law (the same trust model the previous
# jasminc gen_tables.c route used); the comparison oracle ec_msm_ref stays
# table-free (schoolbook double-and-add) and independent.
#
# Targets:
#   make gen_com/msm.s     # OWNED x86-64 emit of ec_msm from Lean (no jasminc)
#   make msm-kat           # build + run the KAT vs the ec_ref.h reference
#
# Legacy (jasminc) targets kept for reference; off the msm-kat critical path:
#   make emit              # (re)emit the old gen/msm.jazz from Lean
#   make gen/ec_tables.jinc# (re)generate the EC dlog tables from ec_ref.h
#   make for-check         # structural check: emitted .jazz has the real `for` loop
#
# Vars:
#   JASMINC=/path/to/jasminc   (default: opam-installed jasminc)
#   CC=gcc

JASMINC ?= $(HOME)/.opam/rocq-9/bin/jasminc
CC      ?= gcc
PIN     ?= taskset -c 0
COMPILER := $(abspath $(CURDIR)/../..)
DEV      := $(abspath $(COMPILER)/../SSProve-lean)
# lake env/build from the dev root (one-root rule); the command runs in the compiler tree
LEAN_IN_COMPILER := cd $(DEV) && lake env sh -c 'cd $(COMPILER) && exec "$$@"' sh

.PHONY: msm-kat emit for-check msm-rustcmd-bench clean

# Re-emit the .jazz straight from the verified front (optional; the committed
# gen/msm.jazz is already the emitter's output).
emit:
	$(LEAN_IN_COMPILER) lean bench/msm_compare/msm_emit.lean

# Regenerate the EC dlog tables (dlog<->point) from the ec_ref.h group law.
gen/ec_tables.jinc: gen_tables.c ec_ref.h
	$(CC) -O2 -I. -o gen/gen_tables gen_tables.c
	./gen/gen_tables > $@

# OWNED emit (no jasminc): the whole ec_msm kernel emitted as one owned x86-64
# leaf via msm_owned_emit.lean (LprogControlFlow.loopLcmd bounded loop +
# LprogAsmPrinter.renderLfundef). The Z/23 EC group law runs in dlog space
# (point-add = +mod28, scalar-mul = *mod28 via Barrett); the DLOG/POW leaf tables
# are passed in by the KAT driver (built from ec_ref.h). KAT'd by msm-kat.
gen_com/msm.s: msm_owned_emit.lean
	ulimit -s unlimited; \
	  $(LEAN_IN_COMPILER) lean --run bench/msm_compare/msm_owned_emit.lean

# Structural check: the emitted .jazz is a REAL single-level `for i = 0 to 8`
# loop (the scalarFold reduction), with the two leaf calls appearing exactly once
# (NOT unrolled to 8 copies) -- mirrors MsmEmit.msm_has_for / msm_not_unrolled.
for-check: gen/msm.jazz
	@grep -q 'for i = 0 to 8' gen/msm.jazz \
	  && echo "for-check: emitted .jazz contains the real 'for i = 0 to 8' MSM loop" \
	  || (echo "for-check: NO MSM loop found" && exit 1)
	@test "$$(grep -c 'ec_scalar_mul(ksi, psi)' gen/msm.jazz)" = "1" \
	  && echo "for-check: scalar-mul leaf appears once (not unrolled to 8 copies)" \
	  || (echo "for-check: scalar-mul leaf unrolled" && exit 1)
	@test "$$(grep -c 'ec_point_add(acc, psi)' gen/msm.jazz)" = "1" \
	  && echo "for-check: point-add leaf appears once (not unrolled to 8 copies)" \
	  || (echo "for-check: point-add leaf unrolled" && exit 1)

# Build and run the KAT against the independent schoolbook EC reference.
msm-kat: gen_com/msm.s msm_kat.c ec_ref.h
	$(CC) -O2 -I. -o msm_kat msm_kat.c gen_com/msm.s
	$(PIN) ./msm_kat

# ---- Tier A rustcmd orchestration bench (one-term lane, shim leaves) ----
# Scope = orchestration overhead, not EC arithmetic; see the .c header.

msm_term_rustcmd_link.s: gen_com/msm_term_from_rustcmd_link.jazz include/msm_leaves.jinc
	$(JASMINC) -arch x86-64 -nowarning -o $@ $<

msm-rustcmd-bench: msm_term_rustcmd_link.s bench_msm_term_from_rustcmd.c
	$(CC) -O2 -o bench_msm_term_from_rustcmd bench_msm_term_from_rustcmd.c msm_term_rustcmd_link.s
	taskset -c 3 ./bench_msm_term_from_rustcmd

clean:
	rm -f gen_com/msm.s gen/ec_tables.jinc gen/gen_tables msm_kat \
	  msm_term_rustcmd_link.s bench_msm_term_from_rustcmd
