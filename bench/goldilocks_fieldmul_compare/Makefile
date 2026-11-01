# Head-to-head: the Goldilocks field multiply goldilocks_mul (single 64-bit field
# element, x = (x*y) mod (2^64 - 2^32 + 1)) emitted by the IN-LEAN x86 backend
# (MULX + two c-folds + a 2-word double conditional subtract — the multi-term
# Solinas reduce SELECTED by ModReduceSelect at c = 2^32 - 1, fuel = 2) vs:
#   - the Plonky3 / winterfell GoldilocksField reduce128 (portable C reference),
#   - GMP mpz (canonical mod-p oracle).
#
#   make            # build the compare binary
#   make run        # build + KAT + bench (pinned to core 3)
#   make TRIALS=2000000 run
#   make emit       # re-emit the .s from the verified Lean AST (run from repo root)
#   make kat        # KAT only (gate)

CC       ?= cc
CFLAGS   ?= -O2 -march=native -mbmi2 -Wall
TRIALS   ?= 2000000
PINCORE  ?= 3

LEAN_S   := gen_com/goldilocks_mul_x86_from_lean.s

COMPILER := $(abspath $(CURDIR)/../..)
# Lake root: a sibling development checkout when present, this repository otherwise.
DEV      := $(or $(wildcard $(abspath $(COMPILER)/../SSProve-lean)),$(COMPILER))
# lake env/build from the dev root (one-root rule); the command runs in the compiler tree
LEAN_IN_COMPILER := cd $(DEV) && lake env sh -c 'cd $(COMPILER) && exec "$$@"' sh

.PHONY: all run kat emit clean

all: goldilocks_mul_compare

# the in-Lean-emitted leaf (assembled by gas; no jasminc in the chain)
lean_gmul.o: $(LEAN_S)
	$(CC) -c $(LEAN_S) -o $@

goldilocks_mul_compare: goldilocks_mul_compare.c lean_gmul.o
	$(CC) $(CFLAGS) goldilocks_mul_compare.c lean_gmul.o -lgmp -o $@

run: goldilocks_mul_compare
	taskset -c $(PINCORE) ./goldilocks_mul_compare $(TRIALS) || ./goldilocks_mul_compare $(TRIALS)

kat: goldilocks_mul_compare
	./goldilocks_mul_compare 1

# Re-emit gen_com/goldilocks_mul_x86_from_lean.s from the verified AST.
emit:
	$(LEAN_IN_COMPILER) lean bench/goldilocks_fieldmul_compare/emit_goldilocks.lean

$(LEAN_S): emit_goldilocks.lean
	$(LEAN_IN_COMPILER) lean bench/goldilocks_fieldmul_compare/emit_goldilocks.lean

clean:
	rm -f lean_gmul.o goldilocks_mul_compare
