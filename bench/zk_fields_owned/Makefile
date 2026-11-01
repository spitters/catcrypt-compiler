# Known-answer tests of the owned x86-64 renderings of the Goldilocks field
# operations, the KoalaBear and Mersenne-31 Poseidon2 permutations and the
# circomlib BN254 Poseidon permutation. See README.md for the ABI of each kernel.
#
# Targets:
#   make gen         build the `zkfieldsowned` exe from the Lake root (DEV)
#                    and render gen/*.s with it
#   make kat         all four KATs
#   make kat-gl      Goldilocks add/sub/mul/neg vs unsigned __int128 mod p
#   make kat-kb      poseidon2_kb vs the Plonky3 KoalaBear width-16 vector
#   make kat-m31     poseidon2_m31 vs the Plonky3 Mersenne-31 width-16 vector
#   make kat-bn254   poseidon_bn254_t3 vs circomlib / Poseidon-reference vectors
#   make clean

CC     ?= cc
CFLAGS ?= -O2 -Wall -Wextra
COMPILER := $(abspath $(CURDIR)/../..)
# Lake root: a sibling development checkout when present, this repository otherwise.
DEV      := $(or $(wildcard $(abspath $(COMPILER)/../SSProve-lean)),$(COMPILER))
# Build-lock wrapper of the development checkout, when there is one.
HEAVY_RUN ?= $(if $(wildcard $(DEV)/scripts/heavy-run.sh),bash scripts/heavy-run.sh)
GEN    := $(CURDIR)/gen

GL_S := $(GEN)/gl_add.s $(GEN)/gl_sub.s $(GEN)/gl_mul.s $(GEN)/gl_neg.s

.PHONY: gen kat kat-gl kat-kb kat-m31 kat-bn254 clean

# One process per kernel: each Poseidon permutation allocates several GB.
KERNELS := gl_add gl_sub gl_mul gl_neg poseidon2_kb poseidon2_m31 poseidon_bn254_t3

gen:
	cd $(DEV) && $(HEAVY_RUN) taskset -c 0-1 lake build zkfieldsowned
	cd $(COMPILER) && ulimit -s unlimited && for k in $(KERNELS); do \
	  $(COMPILER)/.lake/build/bin/zkfieldsowned $(GEN) $$k || exit 1; done

gl_kat: gl_kat.c $(GL_S)
	$(CC) $(CFLAGS) -o $@ gl_kat.c $(GL_S)

poseidon2_kb_kat: poseidon2_kat.c $(GEN)/poseidon2_kb.s
	$(CC) $(CFLAGS) -DFIELD_KB -o $@ poseidon2_kat.c $(GEN)/poseidon2_kb.s

poseidon2_m31_kat: poseidon2_kat.c $(GEN)/poseidon2_m31.s
	$(CC) $(CFLAGS) -DFIELD_M31 -o $@ poseidon2_kat.c $(GEN)/poseidon2_m31.s

poseidon_bn254_kat: poseidon_bn254_kat.c $(GEN)/poseidon_bn254_t3.s
	$(CC) $(CFLAGS) -o $@ poseidon_bn254_kat.c $(GEN)/poseidon_bn254_t3.s

kat-gl: gl_kat
	./gl_kat

kat-kb: poseidon2_kb_kat
	./poseidon2_kb_kat

kat-m31: poseidon2_m31_kat
	./poseidon2_m31_kat

kat-bn254: poseidon_bn254_kat
	./poseidon_bn254_kat

kat: kat-gl kat-kb kat-m31 kat-bn254

clean:
	rm -f gl_kat poseidon2_kb_kat poseidon2_m31_kat poseidon_bn254_kat
