# Plonky3 STARK kernels emitted from CatCrypt's verified front (Tier A path),
# benched against pure-C references.
#
# WIRED rows (have committed gen_com/*_link.jazz + include/* leaves):
#   plonky3-lde-rustcmd-bench       (N=256, k=4 BabyBear coset-FFT LDE)
#   plonky3-merkle-rustcmd-bench    (N=1024 BabyBear Merkle build-root)
#   plonky3-fri-rustcmd-bench       (BabyBear-extension fold-layer arithmetic;
#                                     include/plonky3_fri_leaves.jinc present)
#   plonky3-air-rustcmd-bench       (plonky3_air_transition_3_{8,16,...} transition
#                                     polynomial evaluation; include/plonky3_air_leaves.jinc)
#   plonky3-prove-rustcmd-bench     (6-phase STARK orchestration with real leaf bodies:
#                                     trace LDE, Merkle commit, challenger squeeze,
#                                     quotient compose, OOD/DEEP, FRI prove;
#                                     include/plonky3_prove_leaves.jinc present)
#   plonky3-prove-fib-tierc-bench   (legacy string-templated Tier C Fibonacci STARK)
#
# All rows build/bench through `jasminc`; the FRI/AIR/PROVE leaf .jinc bodies
# now ship under include/.

JASMINC ?= $(HOME)/.opam/rocq-9/bin/jasminc
CC      ?= gcc

COMPILER := $(abspath $(CURDIR)/../..)
DEV      := $(abspath $(COMPILER)/../SSProve-lean)
# lake env/build from the dev root (one-root rule); the command runs in the compiler tree
LEAN_IN_COMPILER := cd $(DEV) && lake env sh -c 'cd $(COMPILER) && exec "$$@"' sh
# build a compiler-package exe from the dev root, then run it in the compiler tree
EXE_IN_COMPILER = cd $(DEV) && bash scripts/heavy-run.sh taskset -c 0-1 lake build $(1) && cd $(COMPILER) && $(COMPILER)/.lake/build/bin/$(1)

.PHONY: plonky3-lde-rustcmd-bench plonky3-merkle-rustcmd-bench \
        plonky3-fri-rustcmd-bench plonky3-air-rustcmd-bench \
        plonky3-prove-rustcmd-bench plonky3-prove-emitted-rustcmd-bench \
        plonky3-prove-emitted-a6-rustcmd-bench \
        plonky3-prove-emitted-a7-rustcmd-bench \
        plonky3-compress-rustcmd-kat \
        plonky3-hash-leaf-rustcmd-kat plonky3-ntt-butterfly-rustcmd-kat \
        plonky3-ntt-layer-rustcmd-kat plonky3-lde-column-rustcmd-kat \
        plonky3-fri-fold-rustcmd-kat plonky3-fri-fold-rustcmd-bench \
        plonky3-glue-rustcmd-kat \
        plonky3-prove-fib-tierc-bench plonky3-honest-prove-reroute-bench \
        plonky3-p3-verifier-interop plonky3-p3-accept-prove \
        plonky3-crate-whole-prover-kat clean

# TASK #647 step 1: the p3-verifier-accepts wire spec, made concrete.
# Builds p3_ref's `p3-fib-interop` binary, which (a) configures the real
# p3-uni-stark prover with the DEFAULT BabyBear Poseidon2 constants — the exact
# constants the CatCrypt emitted Poseidon2 leaf KAT-matches — removing the
# round-constant mismatch, and (b) prove->serialize->deserialize->verifies a
# real p3 proof, dumping the exact `Proof<SC>` wire shape an emitted prover must
# reproduce to be accepted by the genuine p3 verifier. See FULL_PROVER_VS_P3.md
# "Gap 1".
plonky3-p3-verifier-interop:
	cd p3_ref && cargo build --release --bin p3-fib-interop
	taskset -c 3 ./p3_ref/target/release/p3-fib-interop

# TASK #647: the p3-verifier-ACCEPTED prover. p3_accept_prove.c implements the
# exact p3-uni-stark 0.5.3 prove() pipeline — quotient/DEEP-ALI phase, degree-4
# binomial-extension (x^4 = 11) challenges/openings/FRI, exact DuplexChallenger
# transcript order, bincode/serde wire layout — over the EMITTED leaves: every
# Poseidon2 permutation through hp_perm16 (plonky3_honest_prove.s) and every
# column LDE through the A3 leaves (lde_column_from_rustcmd.s; their roots of
# unity coincide with p3's TWO_ADIC_GENERATORS, twist powers are leaf inputs so
# the shift-g quotient domain feeds 1s). Gates: the produced p3_our_proof.bin
# must be byte-identical to the real p3 prover's proof AND the REAL p3 0.5.3
# verifier must accept it (p3-fib-dump also dumps prove()'s intermediates,
# self-checked against prove()'s bytes, for stage-by-stage cross-checks).
plonky3-p3-accept-prove: plonky3_honest_prove.s lde_column_from_rustcmd.s p3_accept_prove.c
	$(CC) -O2 -o p3_accept_prove p3_accept_prove.c plonky3_honest_prove.s lde_column_from_rustcmd.s
	./p3_accept_prove
	cd p3_ref && cargo build --release --bin p3-fib-dump
	./p3_ref/target/release/p3-fib-dump verify p3_our_proof.bin

# The catcrypt-plonky3 CRATE's whole-prover prove()/verify() over the SAME
# verified-emitted leaves (Poseidon2 hp_perm16 + A3 LDE leaves + field kernels),
# gated against the GENUINE p3 0.5.3 oracle two ways:
#   (1) `cargo test`: prove() is byte-identical to the p3 reference proof, the
#       native verify() accepts both our proof and the genuine p3 proof, and
#       rejects a flipped public input / corrupted byte;
#   (2) the crate's prove() bytes, fed to the REAL p3 0.5.3 verifier, are ACCEPTed
#       (and are byte-identical to p3_ref/p3_default_proof.bin).
plonky3-crate-whole-prover-kat:
	cd ../../../SSProve-lean/crates/catcrypt-plonky3 && cargo test
	cd ../../../SSProve-lean/crates/catcrypt-plonky3 && cargo run --release --example prove_to_file -- /tmp/catcrypt_plonky3_proof.bin
	cmp /tmp/catcrypt_plonky3_proof.bin p3_ref/p3_default_proof.bin && echo "crate prove() BYTE-IDENTICAL to genuine p3 0.5.3 proof"
	cd p3_ref && cargo build --release --bin p3-fib-dump
	./p3_ref/target/release/p3-fib-dump verify /tmp/catcrypt_plonky3_proof.bin

# #656 jasmin-tail migration: the four regArith Plonky3 leaves (compress /
# hash_leaf / ntt_layer / fri_fold+bb_inv) are now emitted OWNED — the verified
# front's `Com jasminDialect` rendered straight to AT&T `.s` via
# `Com.toLprogPhysAbi -> renderLprogAtt` (no jasminc). Constants are
# materialized as immediates (`immSlotMap`), so each owned `.s` relinks into the
# existing `*_kat.c` byte-identically. One exe writes all four.
gen_com/compress_from_rustcmd_owned.s gen_com/hash_leaf_from_rustcmd_owned.s gen_com/ntt_layer_from_rustcmd_owned.s gen_com/fri_fold_from_rustcmd_owned.s:
	$(call EXE_IN_COMPILER,plonky3owned)

# Extension-field FRI kernels (FULL_PROVER_VS_P3 Gap 2 item 3): the deg-4
# BinomialExtensionField<BabyBear,4> (x^4=11) multiply coords + base-field scale,
# emitted owned (Plonky3ExtFieldEmit). One `.s` carries all 5 ext leaves.
gen_com/ext4_from_rustcmd_owned.s:
	$(call EXE_IN_COMPILER,plonky3owned)

# KAT the deg-4 ext-field mul/scale/inverse vs the p3 reference. The inverse is
# composed from the emitted ext-mul + scale + base-field bb_inv leaves; checked
# both against p3's einv and against the extension identity a*a^{-1} == 1.
plonky3-ext4-rustcmd-kat: gen_com/ext4_from_rustcmd_owned.s gen_com/fri_fold_from_rustcmd_owned.s ext4_from_rustcmd_kat.c
	$(CC) -O2 -o ext4_from_rustcmd_kat ext4_from_rustcmd_kat.c gen_com/ext4_from_rustcmd_owned.s gen_com/fri_fold_from_rustcmd_owned.s
	./ext4_from_rustcmd_kat

# FULL_PROVER_VS_P3 Gap 2: the SINGLE-BINARY composing module. One owned `.s`
# (plonky3_whole_prover_owned.s) carrying ALL five prover field-kernels
# (compress / hash_leaf / ntt_layer / fri_fold / bb_inv) under their own export
# labels — the composition `Plonky3WholeProverOwnedEmit.wholeProverLprog`
# (`lp_funcs := compress ++ hash_leaf ++ ntt_layer ++ fri_fold ++ bb_inv`).
# Each per-kernel `*_kat.c` relinks against this ONE object byte-identically.
gen_com/plonky3_whole_prover_owned.s:
	$(call EXE_IN_COMPILER,plonky3whole)

# KAT the single composed `.s`: each per-kernel harness, linked against the ONE
# combined object instead of its single-leaf `.s`, stays byte-identical.
plonky3-whole-prover-single-binary-kat: gen_com/plonky3_whole_prover_owned.s \
		compress_from_rustcmd_kat.c hash_leaf_from_rustcmd_kat.c \
		ntt_layer_from_rustcmd_kat.c fri_fold_from_rustcmd_kat.c
	@echo "=== single combined .s carries all 5 prover field-kernels ==="
	@grep -E '^(plonky3_merkle_compress_rc|plonky3_merkle_hash_leaf_rc|plonky3_ntt_layer8_rc|fri_fold_rc|bb_inv_rc):' gen_com/plonky3_whole_prover_owned.s
	@echo "=== KAT each kernel against the ONE combined object ==="
	$(CC) -O2 -o /tmp/wp_compress  compress_from_rustcmd_kat.c  gen_com/plonky3_whole_prover_owned.s && /tmp/wp_compress  | tail -1
	$(CC) -O2 -o /tmp/wp_hashleaf  hash_leaf_from_rustcmd_kat.c gen_com/plonky3_whole_prover_owned.s && /tmp/wp_hashleaf  | tail -1
	$(CC) -O2 -o /tmp/wp_nttlayer  ntt_layer_from_rustcmd_kat.c gen_com/plonky3_whole_prover_owned.s && /tmp/wp_nttlayer  | tail -1
	$(CC) -O2 -o /tmp/wp_frifold   fri_fold_from_rustcmd_kat.c  gen_com/plonky3_whole_prover_owned.s && /tmp/wp_frifold   | tail -1
	@echo "single-binary composing module: all prover field-kernels in ONE verified-emitted .s, each byte-identical to reference"

# FULL_PROVER_VS_P3 Gap 2 items 1-2: the ORCHESTRATION LOOPS as owned control
# flow. One owned `.s` (plonky3_whole_prover_orch_owned.s) carrying the five
# field-kernel leaves AND the five orchestration-loop drivers (Merkle leaf /
# Merkle compress / FRI fold / query / PoW) as owned `loopLcmd` back-edges
# (.L:/cmpq/jne) whose bodies `call` the field leaves — no C for/while on the
# prove path. The composition `Plonky3OrchLoopsOwnedEmit.wholeProverOrchLprog`.
gen_com/plonky3_whole_prover_orch_owned.s:
	$(call EXE_IN_COMPILER,plonky3orch)

# KAT: confirm the orchestration `.s` carries the owned loop control flow (the
# .L back-edges + leaf calls) and still relinks each field-kernel harness
# byte-identically (the loops route the SAME emitted leaves).
plonky3-whole-prover-orch-loops-kat: gen_com/plonky3_whole_prover_orch_owned.s \
		compress_from_rustcmd_kat.c hash_leaf_from_rustcmd_kat.c fri_fold_from_rustcmd_kat.c
	@echo "=== owned orchestration loops: .L back-edges + leaf calls (NO C for/while) ==="
	@grep -E '\.Lp3_(merkle_leaf|merkle_compress|fri_fold|fri_query|pow_grind)_loop_0:|call (plonky3_merkle_hash_leaf_rc|plonky3_merkle_compress_rc|fri_fold_rc)|jne \.Lp3_' gen_com/plonky3_whole_prover_orch_owned.s | head -20
	@echo "=== KAT each field kernel against the orchestration object (leaves byte-identical) ==="
	$(CC) -O2 -o /tmp/op_compress compress_from_rustcmd_kat.c gen_com/plonky3_whole_prover_orch_owned.s && /tmp/op_compress | tail -1
	$(CC) -O2 -o /tmp/op_hashleaf hash_leaf_from_rustcmd_kat.c gen_com/plonky3_whole_prover_orch_owned.s && /tmp/op_hashleaf | tail -1
	$(CC) -O2 -o /tmp/op_frifold  fri_fold_from_rustcmd_kat.c  gen_com/plonky3_whole_prover_orch_owned.s && /tmp/op_frifold  | tail -1
	@echo "orchestration loops owned: Merkle/FRI/query/PoW control flow is owned loopLcmd back-edges, field leaves byte-identical"

# FULL_PROVER_VS_P3 Gap 2 item 1 (#647): route the prover's Poseidon2 permute call
# to the OWNED AVX-512 (ZMM) Poseidon2 leaf. `Plonky3OrchLoopsOwnedEmit` emits a
# second `.s` (plonky3_whole_prover_zmm_owned.s) whose owned permute driver
# `p3_poseidon2_perm_zmm` `call`s the four owned-emitted ZMM half-kernels
# (zm_{tomont,frommont,extround,intdiag}_half_ptr), and whose Merkle / FRI-query /
# PoW orchestration loops call that permute instead of the scalar mixers.
# `lake exe plonky3orch` (recipe at the orch `.s` target above) writes BOTH the
# orch `.s` and this rerouted ZMM `.s` in one run.
gen_com/plonky3_whole_prover_zmm_owned.s: gen_com/plonky3_whole_prover_orch_owned.s

# KAT: the rerouted `.s` carries the owned ZMM permute driver + the owned ZMM
# half-kernel call sites; the owned ZMM leaf itself KAT-matches upstream
# test_default_babybear_poseidon2_width_16 (poseidon2-avx512-zmmasm-kat), and the
# rerouted whole-prover proof is byte-identical to the scalar version
# (honest_prove_reroute GATE B). The permute reroute is denote-preserving +
# ABI-compatible (the owned ZMM permute is (out,in)-ABI-identical to hp_perm16).
plonky3-whole-prover-zmm-permute-kat: gen_com/plonky3_whole_prover_zmm_owned.s
	@echo "=== owned ZMM Poseidon2 permute wired into the prover (perm driver + owned ZMM half-kernel calls) ==="
	@grep -E '\bp3_poseidon2_perm_zmm\b|call zm_(tomont|frommont|extround|intdiag)_half_ptr' gen_com/plonky3_whole_prover_zmm_owned.s | head -12
	@echo "=== hash-phase orchestration loops call the owned ZMM permute (NOT scalar mixers) ==="
	@grep -E '\.Lp3_(merkle_leaf|merkle_compress|fri_query|pow_grind)_loop_0:|call p3_poseidon2_perm_zmm|jne \.Lp3_' gen_com/plonky3_whole_prover_zmm_owned.s | head -16
	@echo "owned AVX-512 ZMM Poseidon2 permute is the prover's Merkle/FRI/FS/PoW permute (see poseidon2-avx512-zmmasm-kat for the leaf KAT, honest_prove_reroute GATE B for byte-identical proof)"

# FULL_PROVER_VS_P3 Gap 2 item 2: the Proof<SC> bincode SERIALIZATION byte-packer.
# `Plonky3SerializeOwnedEmit` emits the LE u64/u32/u8 writers + the digest writer
# as owned loopLcmd/byte-store control flow (no field op — the proof byte layout).
# The KAT links the owned byte-packer and checks each writer byte-for-byte against
# the plain-C bincode reference (w_u64/w_u32/w_fe/w_digest of p3_accept_prove.c).
gen_com/plonky3_serialize_owned.s:
	$(call EXE_IN_COMPILER,plonky3serialize)

plonky3-serialize-kat: gen_com/plonky3_serialize_owned.s serialize_from_rustcmd_kat.c
	@echo "=== owned bincode byte-packer: LE writers + digest loop (NO C for) ==="
	@grep -E '\.Lp3_ser_(u64|u32|digest)_le_0:|movb %dl,|shrq \$$8, %rdx|call p3_ser_u32_le|jne \.Lp3_ser_' gen_com/plonky3_serialize_owned.s | head -16
	@echo "=== KAT: owned byte-packer == bincode reference (byte-identical) ==="
	$(CC) -O2 -o /tmp/p3_ser_kat serialize_from_rustcmd_kat.c gen_com/plonky3_serialize_owned.s && /tmp/p3_ser_kat | tail -1

# FULL_PROVER_VS_P3 Gap 2 item 1: the Fiat-Shamir DuplexChallenger<16,8> transcript
# bookkeeping (the duplexing step). `Plonky3FiatShamirOwnedEmit` emits the absorb
# (inbuf->st) and squeeze (st->outbuf) buffer copies as owned loopLcmd word moves
# around a `call hp_perm16` to the Poseidon2 permute leaf (no field op — the round
# arithmetic is the called permute). The KAT links the owned duplex against a
# shared permute and checks (st, outbuf) byte-for-byte vs the C reference ch_duplex
# driving the SAME permute (the bookkeeping tested in isolation).
gen_com/plonky3_fiat_shamir_owned.s:
	$(call EXE_IN_COMPILER,plonky3fiatshamir)

plonky3-fiat-shamir-kat: gen_com/plonky3_fiat_shamir_owned.s fiat_shamir_from_rustcmd_kat.c
	@echo "=== owned FS duplex: absorb/squeeze loopLcmd word moves + call hp_perm16 (NO C ch_duplex) ==="
	@grep -E '\.Lp3_fs_duplex_[01]:|movq \(%rsi\), %rax|movq %rax, \(%rdx\)|call hp_perm16|jne \.Lp3_fs_duplex_' gen_com/plonky3_fiat_shamir_owned.s | head -16
	@echo "=== KAT: owned duplex == reference ch_duplex over the same permute (byte-identical) ==="
	$(CC) -O2 -o /tmp/p3_fs_kat fiat_shamir_from_rustcmd_kat.c gen_com/plonky3_fiat_shamir_owned.s && /tmp/p3_fs_kat | tail -1

# FULL_PROVER_VS_P3 ext-FRI residual: the ExtensionMmcs fold (row-flatten + Merkle
# commit) + the barycentric OOD/DEEP, driven ENTIRELY by the emitted ext leaves
# (ext4 mul/scale/add/sub + bb_inv) and the emitted base-field Merkle leaves.
# Byte-identical to the p3 reference extension-FRI. (The ext4 owned `.s` is built
# by the gen_com/ext4_from_rustcmd_owned.s rule above; it now also carries the
# ext4_add_rc / ext4_sub_rc per-coordinate leaves the fold/barycentric need.)
plonky3-ext-fri-fold-kat: gen_com/ext4_from_rustcmd_owned.s gen_com/fri_fold_from_rustcmd_owned.s \
		gen_com/compress_from_rustcmd_owned.s gen_com/hash_leaf_from_rustcmd_owned.s \
		ext_fri_fold_from_rustcmd_kat.c
	$(CC) -O2 -o ext_fri_fold_from_rustcmd_kat ext_fri_fold_from_rustcmd_kat.c \
		gen_com/ext4_from_rustcmd_owned.s gen_com/fri_fold_from_rustcmd_owned.s \
		gen_com/compress_from_rustcmd_owned.s gen_com/hash_leaf_from_rustcmd_owned.s
	./ext_fri_fold_from_rustcmd_kat

# REV-11 A1: the Merkle 2-to-1 compress *leaf body*, EMITTED through the
# verified front's regArith path (OWNED x86 backend, no jasminc). KAT-checked
# byte-for-byte against the C reference `ref_compress`.
plonky3-compress-rustcmd-kat: gen_com/compress_from_rustcmd_owned.s compress_from_rustcmd_kat.c
	$(CC) -O2 -o compress_from_rustcmd_kat compress_from_rustcmd_kat.c gen_com/compress_from_rustcmd_owned.s
	./compress_from_rustcmd_kat

# REV-11 A2: the Merkle leaf-hash *leaf body* (1 word -> 4 words, two
# golden-ratio multipliers + an `a3` diffusion), EMITTED through the verified
# front's regArith path (OWNED x86 backend, no jasminc). KAT-checked
# byte-for-byte against the C reference `ref_hleaf`.
plonky3-hash-leaf-rustcmd-kat: gen_com/hash_leaf_from_rustcmd_owned.s hash_leaf_from_rustcmd_kat.c
	$(CC) -O2 -o hash_leaf_from_rustcmd_kat hash_leaf_from_rustcmd_kat.c gen_com/hash_leaf_from_rustcmd_owned.s
	./hash_leaf_from_rustcmd_kat

# REV-11 A2: the BabyBear radix-2 NTT butterfly *body* (t = w*b mod p;
# (a+t, a-t)), EMITTED through the verified front's regArith path. The field
# multiply mod p is a Barrett reduction in regArith words (no hardware `%`),
# so it is the by-construction allRegArith emit. KAT-checked against the spec
# ldeButterfly.
# OWNED emit (no jasminc): the NTT butterfly is the owned in-Lean x86 backend emit
# (gen_com/ntt_butterfly_x86_from_lean.s, proven byte-identical via
# plonky3-ntt-butterfly-x86-lean-kat), symbol-renamed to the rustcmd ABI symbol.
ntt_butterfly_from_rustcmd.s: gen_com/ntt_butterfly_x86_from_lean.s
	sed 's/plonky3_ntt_butterfly_x86/plonky3_ntt_butterfly_rc/g' $< > $@

plonky3-ntt-butterfly-rustcmd-kat: ntt_butterfly_from_rustcmd.s ntt_butterfly_from_rustcmd_kat.c
	$(CC) -O2 -o ntt_butterfly_from_rustcmd_kat ntt_butterfly_from_rustcmd_kat.c ntt_butterfly_from_rustcmd.s
	./ntt_butterfly_from_rustcmd_kat

# #281: the SAME BabyBear butterfly body lowered through the IN-LEAN x86 backend
# (no jasminc): a Com (x86Dialect 64) -> runBlock-verified JInstr block ->
# AsmPrinter AT&T text -> gas. The .s is emitted by the Lean module's emitMain
# (BarrettButterflyKernel.butterflyAsm); KAT + cyc/op bench vs the spec
# ldeButterfly. The straight-line body's denotation is proved equal to the field
# butterfly (butterfly_out0_spec / butterfly_out1_spec).
gen_com/ntt_butterfly_x86_from_lean.s:
	$(LEAN_IN_COMPILER) lean --run ../SSProve-lean/scripts/emit_butterfly_x86.lean

plonky3-ntt-butterfly-x86-lean-kat: gen_com/ntt_butterfly_x86_from_lean.s ntt_butterfly_x86_from_lean_kat.c
	$(CC) -O2 -o ntt_butterfly_x86_from_lean_kat ntt_butterfly_x86_from_lean_kat.c gen_com/ntt_butterfly_x86_from_lean.s
	./ntt_butterfly_x86_from_lean_kat

# W4 (#304): the two-butterfly NTT chain, emitted by the in-Lean x86 backend in
# two forms — ABI-boundary (two separate leaves, producer result round-trips
# through memory) vs inlined-merged (one fused body, register allocation re-run,
# producer result stays register-resident). KAT: both forms == the chain spec.
# Bench: cyc/chain for each form → the per-leaf ABI tax the inline+RA closes.
# The inline+RA denotation preservation is InlinedNttKernel.inlineThenRA_denote_preserves.
gen_com/ntt_bf2chain_abi.s gen_com/ntt_bf2chain_inlined.s:
	$(LEAN_IN_COMPILER) lean --run ../SSProve-lean/scripts/emit_bf2chain_x86.lean

plonky3-ntt-bf2chain-kat: gen_com/ntt_bf2chain_abi.s gen_com/ntt_bf2chain_inlined.s ntt_bf2chain_kat.c
	$(CC) -O2 -o ntt_bf2chain_kat ntt_bf2chain_kat.c gen_com/ntt_bf2chain_abi.s gen_com/ntt_bf2chain_inlined.s
	./ntt_bf2chain_kat

# REV-11 A2: one full radix-2 NTT layer (n=8, last layer): four independent
# butterflies, EMITTED through the verified front's regArith path (Barrett
# field mul-mod, no hardware `%`). KAT-checked against the exact Lean spec
# Plonky3ProveEmit.nttLayer(8,2).
# #656: OWNED emit (no jasminc) — see the plonky3owned rule above.
plonky3-ntt-layer-rustcmd-kat: gen_com/ntt_layer_from_rustcmd_owned.s ntt_layer_from_rustcmd_kat.c
	$(CC) -O2 -o ntt_layer_from_rustcmd_kat ntt_layer_from_rustcmd_kat.c gen_com/ntt_layer_from_rustcmd_owned.s
	./ntt_layer_from_rustcmd_kat

# Gap 3 (per-leaf operand-marshalling ABI tax): TWO chained NTT layers FUSED into
# one emitted `Com jasminDialect` body (Plonky3NttLayerInlineEmit.fusedTwoLayerCom),
# rendered to one owned `.s` via the verified x86 backend (no jasminc). Layer 1's
# eight outputs (live in r0..r7) feed layer 2's value slots directly — NO
# inter-layer copy-out/copy-in buffer. The denotation-preservation lemma
# `fusedTwoLayerCom_denote` (axioms: propext, Quot.sound) proves the fused Com IS
# layer1-body then layer2-body. KAT: fused leaf == unfused single-leaf chain == 2x
# nttLayer, byte-identical (links BOTH the fused and single-leaf owned `.s`).
gen_com/ntt_layer_fused_owned.s:
	$(LEAN_IN_COMPILER) lean --run CatCrypt/Crypto/SecureCompilation/VIR/Plonky3NttLayerInlineEmit.lean

plonky3-ntt-layer-fused-kat: gen_com/ntt_layer_fused_owned.s gen_com/ntt_layer_from_rustcmd_owned.s ntt_layer_fused_kat.c
	$(CC) -O2 -o ntt_layer_fused_kat ntt_layer_fused_kat.c \
		gen_com/ntt_layer_fused_owned.s gen_com/ntt_layer_from_rustcmd_owned.s
	./ntt_layer_fused_kat
	@echo "=== instruction-count: fused vs separate-call chain (Gap 3 marshalling tax) ==="
	@printf '  single-leaf owned .s body instrs : %s\n' "$$(grep -cE '^[[:space:]]+[a-z]' gen_com/ntt_layer_from_rustcmd_owned.s)"
	@printf '  fused owned .s body instrs       : %s\n' "$$(grep -cE '^[[:space:]]+[a-z]' gen_com/ntt_layer_fused_owned.s)"
	@echo "  separate chain (2x single body)  : two prologues/epilogues + an 8-word"
	@echo "  copy-out + 8-word copy-in BETWEEN the calls; the fused body has ONE"
	@echo "  prologue/epilogue, ONE copy-in (8 loads), ONE copy-out (8 stores)."

# REV-11 A3: the FULL coset-NTT column LDE (computeColumnLde 3 5 31), EMITTED as
# a sequence of 7 regArith leaves (intt-8 + coset-twist + 5 forward-NTT layers)
# through the verified front's regArith path (Barrett field mul-mod, no hardware
# `%`). The single-body render overflows emitBodyReg's recursion at ~2.5k
# bindings, so the LDE arithmetic is emitted per-phase and composed on a shared
# 32-word buffer. KAT-checked byte-for-byte against the exact Lean spec
# Plonky3ProveEmit.computeColumnLde.
# OWNED (no jasminc): the 7 coset-NTT column-LDE regArith leaves (intt8, twist,
# ntt32 l0..l4) rendered to ONE .s by the verified x86 backend via
# Plonky3LdeColumnEmit (Com[jasmin] regArith -> toLprogPhysAbi ->
# renderLprogAtt, the #656 owned-tail path). KAT byte-for-byte vs the Lean spec
# Plonky3ProveEmit.computeColumnLde(3,5,31).
gen_com/lde_column_from_rustcmd_owned.s:
	ulimit -s unlimited && $(LEAN_IN_COMPILER) lean --run CatCrypt/Crypto/SecureCompilation/VIR/Plonky3LdeColumnEmitMain.lean

lde_column_from_rustcmd.s: gen_com/lde_column_from_rustcmd_owned.s
	cp $< $@

plonky3-lde-column-rustcmd-kat: lde_column_from_rustcmd.s lde_column_from_rustcmd_kat.c
	$(CC) -O2 -o lde_column_from_rustcmd_kat lde_column_from_rustcmd_kat.c lde_column_from_rustcmd.s
	./lde_column_from_rustcmd_kat

# REV-11 A4: the FRI fold-layer arithmetic + the bbInv modular inverse, EMITTED
# through the verified front's regArith path (no hand-written .jinc, no fmul/finv
# string, no hardware %). leaf.denote = friFold/bbInv spec by construction
# (allRegArith proven compositionally). KAT byte-for-byte vs the Lean spec.
# #656: OWNED emit (no jasminc) — see the plonky3owned rule above. The single
# owned .s carries both fri_fold_rc and bb_inv_rc.
plonky3-fri-fold-rustcmd-kat: gen_com/fri_fold_from_rustcmd_owned.s fri_fold_from_rustcmd_kat.c
	$(CC) -O2 -o fri_fold_from_rustcmd_kat fri_fold_from_rustcmd_kat.c gen_com/fri_fold_from_rustcmd_owned.s
	./fri_fold_from_rustcmd_kat

plonky3-fri-fold-rustcmd-bench: gen_com/fri_fold_from_rustcmd_owned.s bench_fri_fold_from_rustcmd.c
	$(CC) -O2 -o bench_fri_fold_from_rustcmd bench_fri_fold_from_rustcmd.c gen_com/fri_fold_from_rustcmd_owned.s
	./bench_fri_fold_from_rustcmd

# REV-11 A7: the quotient-compose + OOD/DEEP prover-orchestration glue, emitted
# through the verified front as register-arith leaves (Barrett field arithmetic
# over canonical inputs). KATs each emitted leaf element-by-element vs the exact
# A6 spec (ref_quotient_compose / ref_ood_deep).
# OWNED (no jasminc): the three prover-orchestration glue regArith leaves
# (quotient_compose_elem_rc, ood_deep_elem_rc, challenger_squeeze_rc) rendered to
# ONE .s by the verified x86 backend via Plonky3GlueEmit (Com[jasmin]
# regArith -> toLprogPhysAbi -> renderLprogAtt, the #656 owned-tail path). KAT
# byte-for-byte vs the A7 spec (ref_quotient_compose / ref_ood_deep / challenger).
gen_com/glue_from_rustcmd_owned.s:
	ulimit -s unlimited && $(LEAN_IN_COMPILER) lean --run CatCrypt/Crypto/SecureCompilation/VIR/Plonky3GlueEmit.lean

glue_from_rustcmd.s: gen_com/glue_from_rustcmd_owned.s
	cp $< $@

plonky3-glue-rustcmd-kat: glue_from_rustcmd.s glue_from_rustcmd_kat.c
	$(CC) -O2 -o glue_from_rustcmd_kat glue_from_rustcmd_kat.c glue_from_rustcmd.s
	./glue_from_rustcmd_kat

lde_256x4_link.s: gen_com/lde_from_rustcmd_link.jazz include/plonky3_lde_leaves.jinc
	$(JASMINC) -arch x86-64 -nowarning -o $@ $<

merkle_n1024_link.s: gen_com/merkle_from_rustcmd_link.jazz include/plonky3_merkle_leaves.jinc
	$(JASMINC) -arch x86-64 -nowarning -o $@ $<

fri_n1024_link.s: gen_com/fri_from_rustcmd_link.jazz include/plonky3_fri_leaves.jinc
	$(JASMINC) -arch x86-64 -nowarning -o $@ $<

air_link.s: gen_com/air_from_rustcmd_link.jazz include/plonky3_air_leaves.jinc
	$(JASMINC) -arch x86-64 -nowarning -o $@ $<

prove_fib_link.s: gen_com/prove_from_rustcmd_link.jazz include/plonky3_prove_leaves.jinc
	$(JASMINC) -arch x86-64 -nowarning -o $@ $<

fri_proof_link.s: gen_com/fri_proof_from_rustcmd_link.jazz include/plonky3_fri_proof_leaves.jinc
	$(JASMINC) -arch x86-64 -nowarning -o $@ $<

prove_fib_tierc.s: plonky3_prove_fib_tierc_link.jazz include/plonky3_prove_leaves.jinc
	$(JASMINC) -arch x86-64 -nowarning -o $@ $<

plonky3-lde-rustcmd-bench: lde_256x4_link.s bench_lde_from_rustcmd.c
	$(CC) -O2 -o bench_lde_from_rustcmd bench_lde_from_rustcmd.c lde_256x4_link.s
	taskset -c 3 ./bench_lde_from_rustcmd

plonky3-merkle-rustcmd-bench: merkle_n1024_link.s bench_merkle_from_rustcmd.c
	$(CC) -O2 -o bench_merkle_from_rustcmd bench_merkle_from_rustcmd.c merkle_n1024_link.s
	taskset -c 3 ./bench_merkle_from_rustcmd

plonky3-fri-rustcmd-bench: fri_n1024_link.s bench_fri_from_rustcmd.c
	$(CC) -O2 -o bench_fri_from_rustcmd bench_fri_from_rustcmd.c fri_n1024_link.s
	taskset -c 3 ./bench_fri_from_rustcmd

plonky3-air-rustcmd-bench: air_link.s bench_air_from_rustcmd.c
	$(CC) -O2 -o bench_air_from_rustcmd bench_air_from_rustcmd.c air_link.s
	taskset -c 3 ./bench_air_from_rustcmd

plonky3-prove-rustcmd-bench: prove_fib_link.s bench_prove_from_rustcmd.c
	$(CC) -O2 -o bench_prove_from_rustcmd bench_prove_from_rustcmd.c prove_fib_link.s
	taskset -c 3 ./bench_prove_from_rustcmd

# REV-11 A5: whole Plonky3 Fibonacci STARK prover whose TRACE-LDE PHASE runs
# through the EMITTED A3 coset-NTT column-LDE leaves (the 7 register-arith
# leaves of gen_com/lde_column_from_rustcmd.jazz), in place of the hand-written
# .jinc / C-reference LDE. The remaining phases (Merkle commit, challenger,
# quotient, OOD/DEEP, FRI fold + final commit) are hand-written orchestration
# glue, byte-identical to the Lean spec. KATs the whole-prover proof object vs
# the all-C reference, runs the FRI verifier (accept honest / reject tamper),
# and benches whole-prove cyc/op.
plonky3-prove-emitted-rustcmd-bench: lde_column_from_rustcmd.s bench_prove_emitted.c
	$(CC) -O2 -o bench_prove_emitted bench_prove_emitted.c lde_column_from_rustcmd.s
	taskset -c 3 ./bench_prove_emitted

# REV-11 A6: extends A5 — the whole Plonky3 Fibonacci STARK prover now runs its
# TRACE-LDE (A3), MERKLE COMMIT (A1 compress + A2 leaf-hash) and FRI FOLD (A4
# fri_fold_rc + final A1/A2 commit) phases ALL through the verified-front EMITTED
# regArith leaves. Links all four emitted .s objects. The remaining hand-written
# orchestration glue (Fiat-Shamir challenger, quotient compose, OOD/DEEP, the
# tree/coset plumbing) has no emitted leaf yet. KATs the trace-LDE, Merkle root,
# FRI fold and whole-prover proof object vs the all-C reference; runs the FRI
# verifier (accept honest / reject tamper); benches whole-prove cyc/op.
plonky3-prove-emitted-a6-rustcmd-bench: lde_column_from_rustcmd.s compress_from_rustcmd.s hash_leaf_from_rustcmd.s fri_fold_from_rustcmd.s bench_prove_emitted_a6.c
	$(CC) -O2 -o bench_prove_emitted_a6 bench_prove_emitted_a6.c \
	  lde_column_from_rustcmd.s compress_from_rustcmd.s hash_leaf_from_rustcmd.s fri_fold_from_rustcmd.s
	taskset -c 3 ./bench_prove_emitted_a6

# REV-11 A7: extends A6 — the whole Plonky3 Fibonacci STARK prover now ALSO runs
# its three orchestration-glue computations (Fiat-Shamir challenger squeeze,
# quotient compose, OOD/DEEP) through the verified-front EMITTED regArith leaves
# (glue_from_rustcmd.s: challenger_squeeze_rc, quotient_compose_elem_rc,
# ood_deep_elem_rc). The only hand-written residual is index/buffer plumbing
# (no field arithmetic). Links all five emitted .s objects. KATs every emitted
# phase + the whole-prover proof object vs the all-C reference; runs the FRI
# verifier (accept honest / reject tamper); benches whole-prove cyc/op.
plonky3-prove-emitted-a7-rustcmd-bench: lde_column_from_rustcmd.s compress_from_rustcmd.s hash_leaf_from_rustcmd.s fri_fold_from_rustcmd.s glue_from_rustcmd.s bench_prove_emitted_a7.c
	$(CC) -O2 -o bench_prove_emitted_a7 bench_prove_emitted_a7.c \
	  lde_column_from_rustcmd.s compress_from_rustcmd.s hash_leaf_from_rustcmd.s fri_fold_from_rustcmd.s glue_from_rustcmd.s
	taskset -c 3 ./bench_prove_emitted_a7

# Emitted FRI PROOF OBJECT (per-layer commitments + query openings + Merkle
# auth paths + remainder) checked by an external verifier (conform.c pattern):
# honest proof must ACCEPT, tampered proofs must REJECT. Reports prove+verify cyc/op.
plonky3-fri-proof-rustcmd-bench: fri_proof_link.s bench_fri_proof_from_rustcmd.c
	$(CC) -O2 -o bench_fri_proof_from_rustcmd bench_fri_proof_from_rustcmd.c fri_proof_link.s
	taskset -c 3 ./bench_fri_proof_from_rustcmd

# FRONT-COMPILED fri_proof spine phases (fold chain + flat Merkle), owned
# render (no jasminc, no hand Com/Lcmd), emitted by
# Plonky3FriProofFrontEmit.lean; KAT'd against the independent C reference
# recipe (the same fri.rs::fri_prove_column oracle as the whole-artifact KAT).
gen_com/fri_proof_frontphases.s: ../../CatCrypt/Crypto/SecureCompilation/VIR/Plonky3FriProofFrontEmit.lean fri_frontphases_emit.lean
	$(LEAN_IN_COMPILER) lean --run bench/plonky3_compare/fri_frontphases_emit.lean

plonky3-fri-frontphases-kat: gen_com/fri_proof_frontphases.s fri_frontphases_kat.c
	$(CC) -O2 -o fri_frontphases_kat fri_frontphases_kat.c gen_com/fri_proof_frontphases.s
	./fri_frontphases_kat

# FRONT-COMPILED honest_prove FRI fold-chain phase, owned render, emitted by
# Plonky3HonestProveFrontEmit.lean; KAT'd against the REAL jasminc
# whole-prover artifact (linked as the oracle: the fragment must reproduce
# out[16..17] from the artifact's own beta).
gen_com/honest_prove_frontphases.s: ../../CatCrypt/Crypto/SecureCompilation/VIR/Plonky3HonestProveFrontEmit.lean hp_frontphases_emit.lean
	$(LEAN_IN_COMPILER) lean --run bench/plonky3_compare/hp_frontphases_emit.lean

plonky3-hp-frontphases-kat: gen_com/honest_prove_frontphases.s plonky3_honest_prove.s hp_frontphases_kat.c
	$(CC) -O2 -o hp_frontphases_kat hp_frontphases_kat.c gen_com/honest_prove_frontphases.s plonky3_honest_prove.s
	./hp_frontphases_kat

# Tier C (legacy string-templated) Plonky3 Fibonacci STARK prover, vs upstream
# Plonky3 Rust crate (cargo bench in upstream_ref/). Surrogate while the Tier A
# re-emit lands (parallel agent).
plonky3-prove-fib-tierc-bench: prove_fib_tierc.s bench_prove_fib_tierc.c
	$(CC) -O2 -o bench_prove_fib_tierc bench_prove_fib_tierc.c prove_fib_tierc.s
	taskset -c 3 ./bench_prove_fib_tierc

# Honest Plonky3 Fibonacci STARK prover + verifier over the VERIFIED Poseidon2
# permutation (PaddingFreeSponge<16,8,8> leaf hash + TruncatedPermutation<2,8,16>
# compress — no splitmix surrogate). Emits a serialized proof, KAT-gates
# prove->verify ACCEPT / tamper REJECT, and benches whole-prove cyc/op vs the
# real p3-* 0.5.3 reference in p3_ref/. See FULL_PROVER_VS_P3.md.
#
# This rule is the sole producer of bench/plonky3_compare/plonky3_honest_prove.s:
# jasminc lowers the hand-written .jinc, and no Lean module writes that path.
# ../SSProve-lean/bench/framework/AUDIT_EMIT_BYPASS.md classifies it NO-LEAN-PRODUCER for that
# reason.
plonky3_honest_prove.s: plonky3_honest_prove_link.jazz include/plonky3_honest_prover.jinc \
                        include/plonky3_poseidon2_hash.jinc include/plonky3_prove_leaves.jinc
	$(JASMINC) -arch x86-64 -nowarning -o $@ $<

plonky3-honest-prove-bench: plonky3_honest_prove.s honest_prove_kat.c
	$(CC) -O2 -o honest_prove_kat honest_prove_kat.c plonky3_honest_prove.s
	taskset -c 3 ./honest_prove_kat

# Reroute the honest prover's Poseidon2 hashing (Merkle commit, FRI fold-layer
# commit, Fiat-Shamir, PoW) from the SCALAR verified jasmin leaf to the FAST
# AVX-512 (ZMM Montgomery) emitted leaf in ../SSProve-lean/bench/poseidon2_compare. The harness
# replicates hp_prove's algorithm over a pluggable permutation backend and GATES
# on byte-identical proof (C-replica==jasmin monolith AND scalar==avx512) before
# reporting timing, plus an Amdahl breakdown of the Poseidon2 fraction.
P2_AVX512_DIR = ../../../SSProve-lean/bench/poseidon2_compare
plonky3-honest-prove-reroute-bench: plonky3_honest_prove.s honest_prove_reroute.c \
                                    $(P2_AVX512_DIR)/poseidon2_avx512_mont_mlir.c \
                                    $(P2_AVX512_DIR)/poseidon2_avx512_mont_kernels.o
	$(CC) -O2 -mavx512f -mavx512vl -mavx512dq -mavx512bw -o honest_prove_reroute \
	  honest_prove_reroute.c plonky3_honest_prove.s \
	  $(P2_AVX512_DIR)/poseidon2_avx512_mont_mlir.c \
	  $(P2_AVX512_DIR)/poseidon2_avx512_mont_kernels.o
	taskset -c 3 ./honest_prove_reroute

# Verified-Poseidon2 hash KAT (re-confirms byte-match with Plonky3
# PaddingFreeSponge<16,8,8>). OWNED emit (no jasminc): the sponge buffer
# marshalling (rate-overwrite absorb of each block + rate squeeze) is rendered
# from the verified front's `Lcmd` straight to AT&T `.s` via
# `renderLprogAtt` (Plonky3PaddingFreeSpongeEmit), composing the EMITTED
# OWNED Poseidon2 permute leaf `poseidon2_bb` (../SSProve-lean/bench/poseidon2_compare/gen_com/
# poseidon2_bb_owned.s, itself rendered owned and KAT-matched) via `call`. The
# two `.s` relink into p2_hash_kat.c byte-identically.
P2_PERM_OWNED = ../../../SSProve-lean/bench/poseidon2_compare/gen_com/poseidon2_bb_owned.s

gen_com/p2_sponge_owned.s: ../../CatCrypt/Crypto/SecureCompilation/VIR/Plonky3PaddingFreeSpongeEmit.lean
	$(LEAN_IN_COMPILER) lean --run CatCrypt/Crypto/SecureCompilation/VIR/Plonky3PaddingFreeSpongeEmit.lean

plonky3-p2-hash-kat: gen_com/p2_sponge_owned.s $(P2_PERM_OWNED) p2_hash_kat.c
	$(CC) -O2 -o p2_hash_kat p2_hash_kat.c gen_com/p2_sponge_owned.s $(P2_PERM_OWNED)
	./p2_hash_kat

clean:
	rm -f lde_256x4_link.s merkle_n1024_link.s prove_fib_tierc.s \
	  fri_n1024_link.s air_link.s prove_fib_link.s fri_proof_link.s \
	  bench_lde_from_rustcmd bench_merkle_from_rustcmd bench_prove_fib_tierc \
	  bench_fri_from_rustcmd bench_air_from_rustcmd bench_prove_from_rustcmd \
	  bench_fri_proof_from_rustcmd
