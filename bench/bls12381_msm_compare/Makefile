# BLS12-381 G1 multi-scalar multiplication (Pippenger) composed from the three
# landed legs (lean x86 field-mul #490 + AUCurves safegcd inverse #488 +
# Montgomery's-trick batch inversion #481), head-to-head against blst's own
# Pippenger MSM (blst_p1s_mult_pippenger).
#
#   make            # build the compare binary
#   make kat        # KAT only (gate): composed MSM == blst at n=256/1024/4096
#   make run        # KAT + microbench (min-of-5, pinned to core PINCORE)
#
# Legs:
#   field-mul : ../../../SSProve-lean/bench/bls12381_fieldmul_compare/gen_com/bls12381_mont_mul_x86_from_lean.s
#   inverse   : ../../../SSProve-lean/bench/bls12381_safegcd_compare/shim staticlib (bls12_invert_divstep_sat)

CC       ?= cc
CFLAGS   ?= -O2 -march=native -mbmi2 -Wall -Wno-unused-function
REPS     ?= 200
PINCORE  ?= 3

BLST_DIR := ../../../SSProve-lean/bench/reference_install/blst/src
SAFEGCD  := ../../../SSProve-lean/bench/bls12381_safegcd_compare
FIELDMUL := ../../../SSProve-lean/bench/bls12381_fieldmul_compare
LEAN_S   := $(FIELDMUL)/gen_com/bls12381_mont_mul_x86_from_lean.s

MEASLIB_DIR := ../../../SSProve-lean/bench/measurement_lib
include $(MEASLIB_DIR)/Makefile.inc

# AUCurves safegcd staticlib (same as the #488 inverse-vs-blst target; the
# build-emitted .o deps are already bundled inside this archive).
SHIM_DIR  := $(SAFEGCD)/shim
SHIM_LIB  := $(SHIM_DIR)/target/release/libbls12_381_safegcd_shim.a

.PHONY: all kat run clean

all: bls12381_msm_vs_blst

$(MEASLIB_OBJS):
	$(MAKE) -C $(MEASLIB_DIR)

$(SHIM_LIB):
	$(MAKE) -C $(SAFEGCD) shim

lean_blsmontmul.o: $(LEAN_S)
	$(CC) -c $(LEAN_S) -o $@

bls12381_msm_vs_blst: bls12381_msm_vs_blst.c lean_blsmontmul.o \
		$(SHIM_LIB) $(MEASLIB_OBJS)
	$(CC) $(CFLAGS) $(MEASLIB_CFLAGS) -I$(BLST_DIR)/bindings -I$(SAFEGCD) \
	    bls12381_msm_vs_blst.c lean_blsmontmul.o $(MEASLIB_OBJS) \
	    $(SHIM_LIB) $(BLST_DIR)/libblst.a \
	    -lpthread -ldl -lm -o $@

kat: bls12381_msm_vs_blst
	./bls12381_msm_vs_blst 1

run: bls12381_msm_vs_blst
	taskset -c $(PINCORE) ./bls12381_msm_vs_blst $(REPS) || ./bls12381_msm_vs_blst $(REPS)

clean:
	rm -f lean_blsmontmul.o bls12381_msm_vs_blst
