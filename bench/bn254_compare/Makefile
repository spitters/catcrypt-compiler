# Production BN254 (alt-bn128) G1 MSM + EIP-197 pairing-verify kernels emitted
# from CatCrypt's verified front, KAT'd against the AUCurves verified-bedrock2
# reference, anchored to the published EIP-196/EIP-197 generators.
#
#   - bn254_g1_msm (Sum_i k_i * P_i) is the scalarFold reduction over the
#     production BN254 G1 AddCommMonoid (Bn254Emit.g1MsmFold_eq_msm), a real `for`
#     loop calling bn254_g1_scalar_mul / bn254_g1_add.
#   - bn254_eip197_verify is the EIP-197 2-pair product e(P1,Q1)*e(P2,Q2)
#     (two bn254_pairing leaves + one bn254_fp12_mul leaf).
#   - bn254_pairing_one is a single bn254_pairing leaf.
#
# Pipeline:
#   Bn254Emit.Emit.* --(lake env lean bn254_emit.lean)--> gen/*.jazz
#   bn254_kernel.jazz = require bn254_leaves.jinc + gen/*.jazz
#                    --(jasminc -arch x86-64)--> gen/bn254.s
#   bn254_kat.rs --(cargo, links the AUCurves bn254 crate)--> ./bn254_kat
#
# The jazz leaves (bn254_leaves.jinc) are STRUCTURAL stubs realising the leaf
# calling convention so jasminc compiles the emitted kernels over the production
# widths (Fp = 32 bytes, G1 = 64, G2 = 128, Fp12 = 384).  The byte-identical KAT
# runs in Rust against the AUCurves verified leaves (pairing_optimal / fp12_mul).
#
# Targets:
#   make emit        # (re)emit gen/*.jazz from Lean (optional; committed)
#   make gen/bn254.s # jasminc the leaf-linked kernels to x86-64 assembly
#   make for-check   # structural check: emitted G1-MSM has the real `for` loop
#   make kat         # build + run the KAT vs the AUCurves verified reference

JASMINC ?= $(HOME)/.opam/rocq-9/bin/jasminc
AS      ?= as
COMPILER := $(abspath $(CURDIR)/../..)
# Lake root: a sibling development checkout when present, this repository otherwise.
DEV      := $(or $(wildcard $(abspath $(COMPILER)/../SSProve-lean)),$(COMPILER))
# lake env/build from the dev root (one-root rule); the command runs in the compiler tree
LEAN_IN_COMPILER := cd $(DEV) && lake env sh -c 'cd $(COMPILER) && exec "$$@"' sh

.PHONY: kat fp2-kat emit for-check orch-owned clean bn254-vale-bench \
        fp-tower-emit fp-tower-compile fp-tower-kat \
        pairing-emit pairing-kat

emit:
	$(LEAN_IN_COMPILER) lean bench/bn254_compare/bn254_emit.lean

# OWNED emit of the BN254 orchestrations (#656, NO jasminc): the G1 MSM term, the
# single pairing, and the EIP-197 2-pair product check, as SysV pointer-passing
# `call`-orchestrations over the opaque AUCurves leaves, via the array-ABI
# gather/scatter (comToLfundefArrAbi -> renderLprogAtt). Assembles with `as`/`cc`.
gen_com/bn254_orch_owned.s:
	$(LEAN_IN_COMPILER) lean --run ../SSProve-lean/bench/bls12381_compare/ec_pairing_owned_emit.lean

orch-owned: gen_com/bn254_orch_owned.s
	$(AS) --64 -o gen_com/bn254_orch_owned.o gen_com/bn254_orch_owned.s
	@echo "orch-owned: owned BN254 orchestration .s assembled with gas (NO jasminc)"

# Structural check: the owned orchestration .s calls the pairing + GT-mul leaves.
for-check: gen_com/bn254_orch_owned.s
	@grep -q 'call bn254_pairing' gen_com/bn254_orch_owned.s \
	  && echo "for-check: owned orchestration .s calls the bn254_pairing leaf" \
	  || (echo "for-check: NO bn254_pairing call found" && exit 1)
	@grep -q 'call bn254_fp12_mul' gen_com/bn254_orch_owned.s \
	  && echo "for-check: owned orchestration .s calls the bn254_fp12_mul leaf" \
	  || (echo "for-check: NO bn254_fp12_mul call found" && exit 1)

# Build + run the KAT vs the AUCurves verified reference (Rust links AUCurves
# directly; does NOT consume the emitted .s). No jasminc.
kat: bn254_kat.rs Cargo.toml
	cargo run --release --bin bn254_kat

# CONN-3i: emitted Fp2 multiply (schoolbook composition over verified base
# leaves) byte-identical vs the AUCurves verified fp2_mul (bn254_Fp2_mul).
fp2-kat: fp2_kat.rs Cargo.toml
	cargo run --release --bin fp2_kat

# #260: reg-ptr verified-leaf re-emit of the BN254 pairing-tower FIELD arithmetic.
#   - emit the Fp2/Fp6/Fp12 add+mul op bodies (leaf-call chains over the
#     next-lower tower level) through CatCrypt's verified front
#     (translate -> cprogToJasminCom -> emitAbiOrchRegPtr) to reg-ptr .jazz over
#     typed-array (reg ptr u64[N]) field leaves;
#   - jasminc-compile each link-form to x86-64 (clears the AUCurves direct-emit
#     regalloc / address-of-stack-array wall: no inlined byte-pointer multiply in
#     the orchestration);
#   - KAT the emitted leaf-call schedules byte-identical vs the AUCurves verified
#     tower (bn254_Fp2_mul / bn254_Fp6_mul / fp12_mul).
fp-tower-emit:
	$(LEAN_IN_COMPILER) lean bench/bn254_compare/fp_tower_from_rustcmd.lean

fp-tower-compile: fp-tower-emit
	@for f in fp2_add fp2_mul fp6_add fp6_mul fp12_mul; do \
	  $(JASMINC) -arch x86-64 -nowarning gen_com/$${f}_from_rustcmd_link.jazz \
	    -o gen_com/$${f}_tower.s \
	    && echo "fp-tower-compile: $${f} -> x86-64 ($$(wc -l < gen_com/$${f}_tower.s) lines)" \
	    || (echo "fp-tower-compile: $${f} FAILED" && exit 1); \
	done

fp-tower-kat: fp_tower_kat.rs Cargo.toml
	cargo run --release --bin fp_tower_kat

# #260 (#225 follow-on): reg-ptr verified-leaf re-emit of the BN254 pairing
# ALGORITHM steps on top of the field tower.
#   - emit the optimal-ate Miller doubling step (fused line-eval + accumulate, L2),
#     the cyclotomic pow-step and the final-exp easy part (L3) — leaf-call chains
#     over the §8 field-tower leaves plus the Fp2_square/inv, make_line,
#     Fp12_square/conjugate/frobenius leaves — through CatCrypt's verified front
#     (translate -> cprogToJasminCom -> emitAbiOrchRegPtr) to reg-ptr .jazz;
#   - KAT the emitted step leaf-call schedules byte-identical vs an independent
#     reference assembled from the AUCurves verified tower leaves, plus the whole
#     pairing_optimal bilinearity on the published EIP-196/EIP-197 generators.
pairing-emit:
	$(LEAN_IN_COMPILER) lean bench/bn254_compare/pairing_from_rustcmd.lean

pairing-kat: bn254_pairing_kat.rs Cargo.toml
	cargo run --release --bin bn254_pairing_kat

# Perf bench: AUCurves BN254 pairing tower, rdtsc median-of-3
bn254-vale-bench: bn254_vale_bench.rs Cargo.toml
	cargo run --release --bin bn254_vale_bench

clean:
	rm -f gen/bn254.s gen_com/bn254_orch_owned.s gen_com/bn254_orch_owned.o
	cargo clean 2>/dev/null || true
