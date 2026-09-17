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

.PHONY: all emit kat run clean

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

clean:
	rm -f lean_combsel.o comb_select_compare
