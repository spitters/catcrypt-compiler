# ed25519_comb_select_compare — the constant-time Ed25519 comb-window select,
# emitted by the owned x86 backend, checked against a portable constant-time
# reference and timed against it.
#
# The kernel ed25519_comb_select_x86_from_lean (and its 5- and 6-bit window
# variants) is emitted by
# CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel and assembled by
# the system assembler.
#
#   make emit   # re-emit the .s files from the Lean kernel (run from anywhere)
#   make kat    # value check on every secret index
#   make run    # value check, then a pinned microbench
#
# The emitted text is a build output: `emit` lists the emitting module as a
# prerequisite so a stale render is never benchmarked.

CC      ?= cc
CFLAGS  ?= -O2 -march=native
TRIALS  ?= 4000000
PIN     ?= taskset -c 3

REPO    := $(abspath ../..)
KERNEL  := $(REPO)/CatCrypt/Crypto/SecureCompilation/X86Backend/CombSelectKernel.lean
LEAN_S  := gen_com/ed25519_comb_select_x86_from_lean.s

FRONT_S := gen_com_front/ed25519_comb_select_x86_from_lean.s
FRONT_M := $(REPO)/CatCrypt/Crypto/SecureCompilation/X86Backend/CombSelectFront.lean

FOLD_S  := gen_com_folded/ed25519_comb_select_x86_from_lean.s
FOLD_M  := $(REPO)/CatCrypt/Crypto/SecureCompilation/X86Backend/ConstIndexFold.lean

.PHONY: all emit kat run clean emit-front kat-front run-front emit-folded kat-folded run-folded

all: comb_select_compare

$(LEAN_S): $(KERNEL) emit.lean
	cd $(REPO) && lake env lean --run bench/ed25519_comb_select_compare/emit.lean

emit: $(LEAN_S)

lean_combsel.o: $(LEAN_S)
	$(CC) -c $(LEAN_S) -o lean_combsel.o

comb_select_compare: comb_select_compare.c lean_combsel.o
	$(CC) $(CFLAGS) comb_select_compare.c lean_combsel.o -o $@

kat: comb_select_compare
	./comb_select_compare 1

run: comb_select_compare
	$(PIN) ./comb_select_compare $(TRIALS)

# The front-generated select, checked by the same harness. It is not the shipped
# kernel: its table reads are indexed loads, outside the allDirect CT theorem.
$(FRONT_S): $(KERNEL) $(FRONT_M) emit_front.lean
	cd $(REPO) && lake env lean --run bench/ed25519_comb_select_compare/emit_front.lean

emit-front: $(FRONT_S)

front_combsel.o: $(FRONT_S)
	$(CC) -c $(FRONT_S) -o front_combsel.o

comb_select_compare_front: comb_select_compare.c front_combsel.o
	$(CC) $(CFLAGS) comb_select_compare.c front_combsel.o -o $@

kat-front: comb_select_compare_front
	./comb_select_compare_front 1

run-front: comb_select_compare_front
	$(PIN) ./comb_select_compare_front $(TRIALS)

# The front-generated select after the constant-index fold: every table read is a
# fixed-offset load. Not the shipped kernel either.
$(FOLD_S): $(KERNEL) $(FRONT_M) $(FOLD_M) emit_folded.lean
	cd $(REPO) && lake env lean --run bench/ed25519_comb_select_compare/emit_folded.lean

emit-folded: $(FOLD_S)

folded_combsel.o: $(FOLD_S)
	$(CC) -c $(FOLD_S) -o folded_combsel.o

comb_select_compare_folded: comb_select_compare.c folded_combsel.o
	$(CC) $(CFLAGS) comb_select_compare.c folded_combsel.o -o $@

kat-folded: comb_select_compare_folded
	./comb_select_compare_folded 1

run-folded: comb_select_compare_folded
	$(PIN) ./comb_select_compare_folded $(TRIALS)

clean:
	rm -f lean_combsel.o comb_select_compare front_combsel.o comb_select_compare_front \
	  folded_combsel.o comb_select_compare_folded
