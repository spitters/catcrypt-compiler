# Plonky3 full-prover: emitted honest prover vs the real `p3-*` crate

Head-to-head between a CatCrypt-emitted Fibonacci-STARK prover and an
upstream Plonky3 prover built from the `p3-*` 0.5.3 crates.io release. All
numbers are real, same-host, `taskset -c 3`, `rdtsc`, min-of-3.

## TL;DR

| Side | What it is | cyc / full prove |
|---|---|---|
| **Honest emit** (`honest_prove_kat`) | Real verified-Poseidon2 Merkle/FRI/FS + query phase + PoW + serialized proof + verifier | **~3.59M (min), ~3.9M typical** |
| Real `p3-*` 0.5.3 (`p3_ref/`) | Canonical `p3-uni-stark` `prove` over the Fibonacci AIR | **~593k–697k** |
| ~~Legacy Tier C surrogate~~ (`bench_prove_fib_tierc`) | ~~splitmix XOR-multiply stand-in hash, no query phase, no verifier~~ | (artifact — see below) |

**The honest emit prover is ~6× SLOWER than p3, and that is the truth.** Doing
the real verified Poseidon2 hashing (≈7.8k cyc per sponge, in scalar code)
across the whole Merkle tree, the FRI fold-layer tree, the Fiat-Shamir
challenger and the proof-of-work grind costs far more than p3's
AVX2/AVX-512-vectorized Poseidon2. The prior "~60× faster than p3" headline was
**entirely an artifact of NOT doing the work** (surrogate hash + no FRI query
phase + no verifier). With the verified permutation and the missing phases
wired in, the emitted prover lands where an honest scalar STARK prover should:
several× behind a vectorized production prover.

## What changed (the #198 finding, fixed)

The previous "Tier C full prover" was a surrogate shell:
- its Merkle/FRI commit called `_p3_compress_u64` / `_p3_hleaf_u64` — splitmix
  XOR/multiply stand-ins, NOT the verified Poseidon2 permutation;
- it omitted the FRI query phase, PoW grinding, and proof serialization;
- it exposed no verifier.

The honest prover (`include/plonky3_honest_prover.jinc`, `hp_prove`) replaces all
of that:

1. **Verified Poseidon2 on the whole commit path.** Every hash is the real p3
   construction over the verified-emitted Poseidon2-BabyBear permutation:
   - leaf hash = `PaddingFreeSponge<16,8,8>` (`_p2_sponge_row`)
   - 2-to-1 compress = `TruncatedPermutation<2,8,16>` (`_p2_compress`)
   - challenger = duplex sponge over the permutation
   The permutation is copied verbatim from the verified leaf
   `../SSProve-lean/bench/poseidon2_compare/include/poseidon2_leaves.jinc` and **KAT-matches
   Plonky3's `PaddingFreeSponge<16,8,8>` digest exactly**
   (`p2_hash_kat`: digest == Plonky3, 8/8 lanes).
2. **Missing phases emitted.** Real trace LDE (coset NTT-32), a full depth-5
   Merkle commit of the 32 LDE rows (nodes retained for auth paths), a FRI fold
   chain 32→16→8→4→2 with a committed fold-layer Merkle tree, an 8-query FRI
   **query phase** (open each query at the codeword tree and the fold-layer tree
   with full Merkle authentication paths), and an 8-bit **proof-of-work grind**.
3. **Verifiable serialized proof + verifier.** `hp_prove` writes a flat 980-lane
   proof (roots, FRI final poly, beta, PoW nonce, 8 query openings + auth paths).
   The verifier (`honest_prove_kat.c::hp_verify`) recomputes every Merkle root
   from the openings, re-derives the Fiat-Shamir challenges, checks the FRI fold
   relation at each query, and checks the PoW — **its hashing is done by calling
   the SAME emitted verified leaves** (`hp_sponge8`/`hp_compress8`/`hp_perm16`),
   not a C re-implementation.

## Circuit (matched as closely as the two APIs allow)

| Parameter | Honest emit | `p3-*` reference |
|---|---|---|
| Field | BabyBear | BabyBear |
| AIR | Fibonacci | Fibonacci (verbatim from `p3-uni-stark` 0.5.3) |
| Trace height | 8 | 8 (`1<<3`) |
| Trace width | 3 (`a,b,c=a+b`) | 2 (`left,right`) |
| Public values | `(a=0,b=1,c_last)` bound into Fiat-Shamir | `[0,1,21]` |
| Hash | Poseidon2-BabyBear-16, `PaddingFreeSponge<16,8,8>` + `TruncatedPermutation<2,8,16>` | same families |
| Merkle | depth-5 tree over 32 LDE rows | `MerkleTreeMmcs` |
| FRI | blowup 4 (domain 32), 8 queries, PoW 8 bits, fold-layer tree | `log_blowup=2`, `num_queries=8`, `TwoAdicFriPcs` |

Note: the round constants differ from `p3_ref` (which seeds its permutation from
`SmallRng(1)` rather than the default BabyBear constants), so a byte-identical
proof comparison across the two binaries is not meaningful — but our hashing IS
the verified default-constant Poseidon2, KAT-matched to Plonky3's own
`PaddingFreeSponge<16,8,8>` vector. The emit prover is self-consistent: its own
verifier accepts its own honest proof and rejects tampering.

## KAT / verify-accept gate

**Honest emit (`honest_prove_kat`):**
```
KAT: verify ACCEPT on honest proof              [PASS]
KAT: verify REJECT on tampered public input     [PASS]
```
The verifier accepts the honest proof and rejects a flipped public input
(claimed 8th-row Fibonacci value `c_last` → `c_last+1`): the tampered public
value changes the Fiat-Shamir transcript (it is absorbed before beta and the
query indices are squeezed), so beta and the query set do not match the
proof's recorded values and the Merkle/FRI checks fail.

**Real `p3-*` reference (`p3_ref/`):**
```
KAT: verify ACCEPT on honest proof              [PASS]
KAT: verify REJECT on tampered public input     [PASS]
```

**Verified-Poseidon2 hash KAT (`p2_hash_kat`):**
```
digest[0..8] == Plonky3 PaddingFreeSponge<16,8,8>   [PASS]
```

## What fraction is verified-Poseidon2

- **Hashing (Merkle commit, FRI fold-layer commit, Fiat-Shamir, PoW): 100%
  through the verified Poseidon2 permutation.** No splitmix surrogate anywhere
  on the honest path. The permutation KAT-matches Plonky3.
- **Field layer (BabyBear arithmetic + coset NTT LDE): verified-emitted**
  (the `_pr_*` ops and the radix-2 coset NTT, byte-for-byte the Lean spec).
- **FRI structure**: a real fold chain + a committed fold-layer Merkle tree +
  an 8-query opening phase with full authentication paths + PoW. This is a
  single-fold-tree demonstrator (one committed intermediate layer `f16` plus a
  length-2 final polynomial), not the full multi-layer commit-per-fold that p3
  emits; the soundness-critical per-query Merkle + fold-consistency check is
  real and gated.
- **Still simpler than p3**: p3 uses a 4-element extension field for FRI
  challenges, commits a Merkle tree at every fold layer, and batches PCS
  quotient openings across multiple matrices; the emit prover uses the base
  field for the FRI challenge and commits one fold-layer tree. The emit prover
  is therefore an honest, sound-shaped STARK over the verified hash, not a
  drop-in re-implementation of p3's exact PCS.

## Honest bench

```
Honest emit prove (jasminc): ~3.59M cyc/op (min-of-3), ~3.9M typical
Real p3-* 0.5.3 prove:       ~0.59M cyc/op (min-of-3)
ratio: emit is ~6x SLOWER than p3
```

The ~6× gap is the cost of (a) scalar verified Poseidon2 vs p3's vectorized
Poseidon2 and (b) the PoW grind. This is the honest figure with real hashing in
place — there is no "speedup."

## Reproduce

Honest emit prover + verifier (KAT-gated, then bench):
```
cd bench/plonky3_compare
make plonky3-honest-prove-bench      # jasminc emit + gcc + run
make plonky3-p2-hash-kat             # verified Poseidon2 == Plonky3 sponge KAT
```

Real `p3` reference:
```
cd bench/plonky3_compare/p3_ref
cargo build --release
taskset -c 3 ./target/release/p3-fib-ref
```

Host: same machine, single core `-c 3`, run sequentially. Toolchain:
`cargo 1.93.0`, `rustc 1.93.0`, `-O3` + fat LTO; jasminc from `rocq-9`.

## Poseidon2 reroute: scalar leaf -> fast AVX-512 leaf (the #647 lever)

The honest prover above runs the verified Poseidon2 permutation in **scalar**
jasmin (jasmin's word model caps at U256, so it cannot emit ZMM). The
permutation is ~97% of the whole prover. Rerouting the prover's Poseidon2 calls
(Merkle trace-commit, FRI fold-layer commit, Fiat-Shamir challenger, PoW grind)
to the **fast AVX-512 (ZMM 8-lane Montgomery) emitted leaf**
(`../SSProve-lean/bench/poseidon2_compare/poseidon2_avx512_mont_mlir.c` over
`poseidon2_avx512_mont_kernels.o`, the #287 MLIR + `llc -O3` lowering, at ~0.85x
of Plonky3 production) gives a near-full prover-level speedup. The #288 lowering
of the same kernel through CatCrypt's own x86(+ZMM) backend
(`gen_zmmasm/poseidon2_avx512_zmm_kernels.s`) measures 1.075x and is not what
this target links.

`honest_prove_reroute.c` replicates `hp_prove`'s exact algorithm over a pluggable
permutation backend and gates on byte-identical proof before timing:

```
GATE A  C-replica(scalar) == jasmin-monolith hp_prove : byte-identical [PASS]
GATE B  AVX-512-rerouted proof == scalar proof        : byte-identical [PASS]
  proof root0[0]=1902249559  nonce=99   (Poseidon2 perms / prove = 209)

  scalar-Poseidon2 prover : ~3.51M cyc/op
  avx512-Poseidon2 prover : ~0.54M cyc/op
  prover speedup (scalar/avx512): ~6.4x

  raw perm: scalar ~16.3k cyc/perm  avx512 ~2.4k cyc/perm  (~6.7x)
  Poseidon2 share of prover: scalar ~97%, avx512 ~93%
  non-Poseidon2 (LDE/FRI arith/serialize): ~3%
```

Both backends compute the identical Poseidon2-BabyBear permutation (each
KAT-matches the same upstream `test_default_babybear_poseidon2_width_16`), so the
serialized proof is unchanged (same `root0`, same PoW `nonce=99`).

**Amdahl / honesty.** Poseidon2 is ~97% of the prover, so the kernel win carries
almost fully (6.4x prover vs 6.7x raw perm). There is **no** scalar non-Poseidon2
wall: the FRI/LDE/serialize field arithmetic is only ~3%. The PoW grind is itself
Poseidon2 (this trace: nonce=99 -> ~100 of the 209 perms; the fixed commit/FRI/FS
work is the other ~109), so it is sped up by the AVX-512 leaf too rather than
becoming a residual scalar cost. The rerouted prover at ~0.54M cyc/op now lands
**at parity with / slightly under** the real `p3-*` 0.5.3 reference (~0.59M),
where the scalar prover was ~6x behind.

Caveat: this is the prover *algorithm* rerouted in C orchestration over the fast
emitted permutation leaf; the fully-emitted jasmin monolith `hp_prove` still
inlines the scalar permutation (jasmin can't emit ZMM), so a single-binary
fully-emitted AVX-512 prover needs the MLIR/x86-ZMM backend to own the whole
prover orchestration, not just the permutation leaf. The number here is the
honest ceiling the reroute unlocks, gated to byte-identical proof.

Reproduce: `make plonky3-honest-prove-reroute-bench`.

## The two completeness gaps (TASK #647)

The reroute closes the *perf* gap (parity with p3). Of the two *completeness*
gaps, Gap 1 (p3-verifier-accepts) is closed at the C-orchestration-over-
emitted-leaves level; Gap 2 (single emitted binary) remains open.

### Gap 1 — p3-verifier-accepts: CLOSED (C orchestration over emitted leaves)

`p3_accept_prove.c` implements the exact `p3-uni-stark` 0.5.3 `prove()`
pipeline for the interop config (DEFAULT BabyBear Poseidon2 constants — the
constants the emitted leaf KAT-matches; `log_blowup=2`, `log_final_poly_len=2`,
`max_log_arity=1`, 8 queries, 0 PoW bits) and its proof **is accepted by the
real p3 verifier**:

```
make plonky3-p3-accept-prove
  wrote p3_our_proof.bin (4949 bytes)
  byte-compare vs in-process real prove(): IDENTICAL (4949 vs 4949 bytes)
  REAL p3 verifier on candidate proof: ACCEPT
```

The proof is **byte-identical** to the proof the upstream `p3-*` 0.5.3 prover
emits for the same trace/config (`cmp p3_our_proof.bin p3_ref/p3_default_proof.bin`),
and a 1-byte tamper is REJECTed by the real verifier
(`InvalidOpeningArgument(InputError(CapMismatch))`).

What the prover contains (the three items formerly missing):

1. **Quotient / DEEP-ALI phase.** Folded AIR constraints (5 Fibonacci
   constraints weighted by descending powers of the extension challenge
   `alpha`, p3's `ConstraintLayout::decompose_alpha` order) evaluated on the
   disjoint coset `gH` with p3's `selectors_on_coset`, divided by the zerofier
   `Z_H`; the extension-valued quotient flattened to 4 base columns
   (`flatten_to_base`), LDE'd onto `gK` and Merkle-committed
   (`commit_quotient`); trace and quotient opened at `zeta` / `zeta·h` by
   barycentric interpolation over the bit-reversed coset.
2. **Degree-4 extension-field FRI.** `BinomialExtensionField<BabyBear,4>`
   (binomial `x^4 = 11`) arithmetic including inverse (Frobenius/norm);
   `alpha`, `zeta`, FRI batch `alpha`, fold `beta` sampled as extension
   elements; reduced openings `Σ α^k (Mred(z) − Mred(x))/(z − x)` over the
   extension; the arity-2 fold layer committed as an `ExtensionMmcs`
   (flattened 16×8 base rows); 4-element extension `final_poly` via size-4
   inverse DFT.
3. **Exact transcript + wire format.** Faithful `DuplexChallenger<16,8>`
   (overwrite-mode duplexing, pop-from-end sampling, `sample_bits(5)` query
   indices, `grind(0)` = zero witness with no transcript effect), p3's exact
   observe/sample order, and the bincode 1.x serde layout of `Proof<SC>`
   (monty-form `u32` field elements, fixint `u64` lengths, byte Options).

Emitted-leaf coverage inside this prover:

- **All Poseidon2 permutations** (Merkle leaf hash `PaddingFreeSponge<16,8,8>`,
  2-to-1 `TruncatedPermutation<2,8,16>`, Fiat-Shamir duplexing) run through the
  verified-emitted jasmin leaf `hp_perm16` (`plonky3_honest_prove.s`).
- **All column LDEs** (trace and quotient) run through the emitted A3 leaves
  (`lde_column_from_rustcmd.s`): their roots of unity `31^((p−1)>>k)` equal
  p3's `TWO_ADIC_GENERATORS`, and the twist powers are leaf *inputs*, so the
  shift-`g` quotient domain is handled by feeding 1s. Each leaf composition is
  cross-checked in-binary against the plain-C reference.
- The barycentric OOD evaluation, constraint fold, FRI fold, and serialization
  remain C orchestration in `p3_accept_prove.c`. The **extension-field
  arithmetic kernels are now emitted** (see below): the deg-4
  `BinomialExtensionField<BabyBear,4>` multiply, the base-field scale/Frobenius,
  and the Frobenius/norm inverse run through the verified front.

### Degree-4 extension-field FRI kernels: EMITTED (KAT vs p3 reference)

`CatCrypt/Crypto/SecureCompilation/VIR/Plonky3ExtFieldEmit.lean` emits the deg-4
binomial-extension (`x^4 = 11`) field kernels through the verified front's
register-arith path (the same `emitBBMul`/`emitBBAdd`/`emitBBSub` Barrett builder
as the A4/A7 leaves), owned-rendered to `gen_com/ext4_from_rustcmd_owned.s`:

* `ext4_mul_c0_rc … ext4_mul_c3_rc` — the four coordinates of `emul`
  (`c0 = a0·b0 + 11·(a1·b3+a2·b2+a3·b1)`, etc.), each one verified-emitted leaf;
* `ext4_scale_rc` — the base-field coordinate scale (covers `escale` / the
  Frobenius coefficient multiply `efrob`).

Each leaf is `allRegArith` (`ext_field_all_regarith_only`, via the `RegTail`
main theorem), so its denotation IS the Barrett word arithmetic — by-construction
`leaf.denote = spec`, no `sorry`, axioms `[propext, Quot.sound]` only.

The **Frobenius/norm inverse** `einv` is composed from these emitted leaves plus
the existing base-field `bb_inv_rc` (Fermat `a^(p-2)`) for `finv(norm)` — so the
entire ext-field inverse is emitted-leaf arithmetic.

KAT (`make plonky3-ext4-rustcmd-kat`), vs the p3 reference
(`p3_accept_prove.c`'s `emul`/`escale`/`efrob`/`einv`, transcribed from p3's
`BinomialExtensionField`):

```
ext4 multiply (all 4 coords) == p3 emul        [PASS]
ext4 scale/Frobenius == p3 escale/efrob        [PASS]
ext4 inverse (Frobenius/norm) == p3 einv       [PASS]
ext4 inverse identity a*a^{-1} == 1            [PASS]
```

### Extension-FRI fold + barycentric OOD/DEEP: EMITTED (KAT vs p3 reference)

The `ExtensionMmcs` fold and the barycentric OOD/DEEP-over-extension evaluation
are now driven ENTIRELY by emitted leaves. `Plonky3ExtFieldEmit` adds the two
remaining per-coordinate ext operations — `ext4_add_rc` (`eadd`) and
`ext4_sub_rc` (`esub`), each an `allRegArith` base-field `bbAdd`/`bbSub` leaf — so
the full ext-op set the fold and barycentric use is emitted:

| ext op   | emitted leaf(s)                              |
|----------|----------------------------------------------|
| `emul`   | `ext4_mul_c0_rc … ext4_mul_c3_rc`            |
| `escale` | `ext4_scale_rc`                              |
| `eadd`   | `ext4_add_rc`                                |
| `esub`   | `ext4_sub_rc`                                |
| `einv`   | `emul` + `escale` + `bb_inv_rc`              |

The ExtensionMmcs fold (`folded16[r] = escale(eadd(lo,hi),inv2) +
escale(emul(esub(lo,hi),β),hip[r])`), the 16×2-ext → 16×8 base **row flatten**
(structural lane interleave), the **Merkle commit** of the flattened rows (the
existing base-field `plonky3_merkle_compress_rc`/`plonky3_merkle_hash_leaf_rc`
leaves), and the barycentric reduced-opening loop all run through emitted leaves.

`Plonky3ExtFriFoldEmit.lean` re-exports the full ext-op `allRegArith` set
(`ext_fri_all_ops_emitted`) and pins the owned `.s` export labels
(`extFri_owned_has_add_sub`), `[propext, Quot.sound]`-only, no `sorry`.

KAT (`make plonky3-ext-fri-fold-kat`), vs the p3 reference extension-FRI
(`ext_fri_fold_from_rustcmd_kat.c`, transcribed from `p3_accept_prove.c`):

```
barycentric reduced openings (32 rows) == p3 ref      : PASS
ExtensionMmcs fold (16 folded ext elems) == p3 ref    : PASS
ExtensionMmcs commit root (flattened 16x8 base) == ref: PASS
ext inverse (Frobenius/norm) consistency              : PASS
```

**Precise residual**: the only remaining C is the *index plumbing* of the row
flatten / commit (which rows feed which commit node) — pure array indexing, no
field op — and that loop is itself the Merkle tree-level loop emittable as the
owned `loopLcmd` orchestration (`Plonky3OrchLoopsEmit`, below). The deg-4
extension-FRI field-op layer (mul + scale + add + sub + inverse + fold +
barycentric) is closed: every ext operation is an emitted leaf.

Cross-check tooling: `p3_ref/src/interop_dump.rs` (`p3-fib-dump`) replicates
`prove()` stage by stage through public p3 APIs, asserts the replication is
byte-identical to `prove()`'s proof, and dumps every intermediate (trace LDE
rows, commitments, `alpha`, selectors, quotient values, `zeta`, opened values,
FRI alpha/beta, final poly, query indices) in canonical form;
`p3-fib-dump verify <file>` runs the REAL verifier on a foreign proof file.
The C prover prints the same intermediates — every stage agrees.

### Gap 2 — fully-emitted single-binary ZMM orchestration: BLOCKED (wiring), pieces exist

The reroute is C orchestration over the fast AVX-512 leaf; it is not a single
emitted binary. Assessment of whether the owned MLIR/x86-ZMM backend can own the
whole `prove()` (LDE→Merkle→quotient→DEEP→FRI loop):

**The building blocks all exist in the owned backend:**
- ZMM/AVX-512 ops are emitted by the **verified** x86 backend: `JasminDialect`'s
  `vpackZMM` + `WSize.U512` (#286), and the 4 single-pass-Montgomery lane
  kernels via `X86Backend/Avx512*` (#288) /
  `VIR/Poseidon2Avx512{,Jasmin}.lean` (#283/#287). Jasmin's U256 word cap is
  lifted for these ops.
- Bounded + **looped** (non-unrolled, back-edge `jne .L`) control flow is
  emitted by the owned backend with denotation-preservation proven:
  `X86Backend/LprogControlFlow.lean` (#538), `X86Backend/ScfDialect.lean`
  (#566), `X86Backend/LoopUnroll.lean`, worked end-to-end at runtime-N in
  `X86Backend/MpnLoopEmit.lean` (#500).
- The Plonky3 prover **phases** are already emitted as straight-line
  `Com jasminDialect` leaves through the verified front (REV-11 A1–A7):
  Merkle compress/leaf-hash, coset-NTT column LDE, FRI fold, and the
  orchestration glue (Fiat-Shamir squeeze, quotient compose, OOD/DEEP) in
  `VIR/Plonky3{Compress,Glue,NttButterfly}Emit.lean`; the whole Poseidon2
  permutation as a flat `Com` in `VIR/Poseidon2WholePermCom.lean`.

**The exact blocker.** No module composes these into ONE top-level `prove` `Com`
emitted as a single binary. Even the most-emitted driver
(`bench_prove_emitted_a7.c`) keeps the **host-side `for`/`while` loop drivers
that gather operands and route the emitted leaves** in hand-written C — its own
header states these "carry no [proof]". So today the prover is: emitted ZMM
Poseidon2 lane kernels + emitted scalar field/phase leaves, **stitched by
unverified C loops**. Three pieces of integration work are missing, in order:

1. **A whole-prover ZMM `Com`/`Lprog`** that threads the state through the
   ZMM Poseidon2 permutation (compose `Poseidon2WholePermCom`'s scalar Com with
   the `vpackZMM` lane ops — the lane kernels exist but no module assembles the
   *full* permutation in ZMM, only the MDS-add lane op end-to-end).
2. **The orchestration loops as `scf.for`/looped `Lcmd`** (the Merkle tree-build
   levels, the FRI fold chain, the 8-query loop, the PoW `while`) carried as
   owned-backend control-flow ops instead of C `for`/`while` — the dialect ops
   (`ScfDialect.forN/ifTE`, `LprogControlFlow.loopLcmd`) exist but are not
   instantiated for these specific loop bodies.
3. **A single `toLprogPhysAbi` emit** of that composed `Com` to one `.s`, KAT-gated
   to the same proof bytes the reroute produces.

Status: **BLOCKED on integration, not on backend capability.** Every primitive
(ZMM lane ops, verified looped control flow, the phase leaves) is present and
proven; what is missing is a module that *composes* them into one emitted prover
and the `.s` emit + KAT. This is bounded, scoped work — not a backend gap.
(The reroute's ~0.54M cyc/op remains the honest perf ceiling this would realize
in a single binary.)

### Gap 2 — the composing module: LANDED (single `.s`, all field-kernels), loops residual

The missing composing module is built:
`CatCrypt/Crypto/SecureCompilation/VIR/Plonky3WholeProverEmit.lean`
(`lake exe plonky3whole`). It composes the five owned phase-leaf `Lprog`s into
ONE `Lprog` —
`wholeProverLprog.lp_funcs := compress ++ hash_leaf ++ ntt_layer ++ fri_fold ++ bb_inv` —
and renders it to **one `.s`** (`gen_com/plonky3_whole_prover_owned.s`) through
`renderLprogAtt`. This is the same multi-func-into-one-object composition the
owned Blake2b/ChaCha emitters use; each function keeps its own export label.

KAT (`make plonky3-whole-prover-single-binary-kat`): every per-kernel harness
(`compress_from_rustcmd_kat.c`, `hash_leaf_…`, `ntt_layer_…`, `fri_fold_…`),
relinked against the **single combined object** instead of its single-leaf `.s`,
stays **byte-identical to reference** — all PASS. The combined `.s` is the
per-leaf objects concatenated (66 495 B ≈ 2158+1860+4775+57699), so the
byte-identity carries over.

In-Lean shape lemmas (`wholeProver_shape`, `wholeProver_funcs_eq`,
`wholeProver_func_count`) pin that the one object carries all five export labels,
contains no `# UNHANDLED-OP`, and is exactly the five leaves' functions in order
— `[propext, Quot.sound]`-only, no `sorry`.

**What this closes**: the field-arithmetic kernel set of the whole prover is now
ONE verified-emitted object, one driver / one link line (no per-leaf `.s` list).
This is the substantive half of Gap 2 item 3 ("a single `toLprogPhysAbi` emit
of that composed `Com` to one `.s`, KAT-gated").

### Gap 2 items 1–2 — orchestration loops as owned control flow: LANDED

`CatCrypt/Crypto/SecureCompilation/VIR/Plonky3OrchLoopsEmit.lean`
(driver: `Plonky3OrchLoopsEmitMain.lean`, `lake exe plonky3orch`)
emits the orchestration LOOPS as owned-backend looped
`Lcmd` through `LprogControlFlow.loopLcmd` (#538). Each loop is a single body
copy wrapped in the back-edge shape `.L<top>: … ; subq $1,%r8 ; jne .L<top>`,
constant-size in the trip count, whose body is an `LinstrR.Lcall` to the emitted
phase leaf (the same intra-object `call <leaf>` the X25519 ladder uses) plus the
operand-pointer advance — pure index/counter arithmetic, no field op:

| orchestration loop      | owned back-edge body call            |
|-------------------------|--------------------------------------|
| Merkle leaf level (×32) | `call plonky3_merkle_hash_leaf_rc`   |
| Merkle compress levels  | `call plonky3_merkle_compress_rc`    |
| FRI fold chain          | `call fri_fold_rc`                   |
| FRI query loop (×8)     | `call plonky3_merkle_compress_rc`    |
| PoW grind `while`       | `call plonky3_merkle_hash_leaf_rc`   |

The composed `wholeProverOrchLprog` carries BOTH the five field-kernel leaves AND
the five orchestration-loop drivers, rendered to ONE `.s`
(`gen_com/plonky3_whole_prover_orch_owned.s`) — the prove path's control flow is
owned `loopLcmd` back-edges, NOT C `for`/`while`. Shape lemmas
(`merkleLeafLoop_renders_control_flow`, `friFoldLoop_renders_control_flow`,
`powGrindLoop_renders_control_flow`, `orchLoop_length`, `orchLoop_calls_leaf`,
`wholeProverOrch_shape`/`_funcs_eq`/`_func_count`) pin that each loop renders the
`.L:`/`cmp`/`jne` back-edge with its `call <leaf>` body, is constant-size in the
trip count (`looped_shorter_than_unrolled`), and that the one object carries
every leaf + every loop. `[propext, Classical.choice, Quot.sound]` + the
`native_decide` tier, no `sorry`.

KAT (`make plonky3-whole-prover-orch-loops-kat`): the orchestration `.s` carries
the owned loop control flow (the `.L` back-edges + leaf calls), and each
field-kernel harness relinks against the orchestration object byte-identically
(the loops route the SAME emitted leaves) — all PASS.

**Precise residual**: the *initial buffer marshalling* before the first loop (the
straight-line setup that lays out the LDE rows / Fiat-Shamir transcript bytes) is
not itself a loop and stays in the driver prologue — it carries no field op and
no control flow. The denotation of each emitted loop is `runBoundedLoop` (the
bounded counter semantics `LoopUnroll`/`ScfDialect` prove), so the owned looped
emission and a C `for` over the same body agree by construction.

### Gap 2 item 2 — `Proof<SC>` bincode SERIALIZATION as owned byte-packer: LANDED

`CatCrypt/Crypto/SecureCompilation/VIR/Plonky3SerializeEmit.lean`
(`lake exe plonky3serialize`) emits the `Proof<SC>` bincode 1.x byte layout —
phase 5 of `p3_accept_prove.c` — as owned-backend `Lcmd` through the verified
linear printer. The serializer is **pure byte-marshalling**: little-endian length
prefixes, byte `Option` tags, and the LE byte-split of each `u32`/`u64`. The only
field op anywhere in the serializer is the `monty(x)` Barrett-by-constant multiply
inside `w_fe` — an already-emitted leaf shape — so the byte-packer itself is
field-op-free (it serializes a value already in monty/u32 form).

The owned writers, one `.s` (`gen_com/plonky3_serialize_owned.s`):

| serializer primitive (`p3_accept_prove.c`) | owned function     | shape                              |
|---------------------------------------------|--------------------|------------------------------------|
| `w_u64(v)` — 8 LE bytes                      | `p3_ser_u64_le`    | `loopLcmd` ×8: `movb %dl ; shrq $8`|
| `w_u32(v)` (= `w_fe` bytes) — 4 LE bytes     | `p3_ser_u32_le`    | `loopLcmd` ×4: `movb %dl ; shrq $8`|
| `w_u8(v)` — one byte                         | `p3_ser_u8`        | straight-line `movb %dl, (%rdi)`   |
| `w_digest(d[8])` — 8 × `w_fe`               | `p3_ser_digest_le` | `loopLcmd` ×8: `call p3_ser_u32_le`|

Each LE writer is the verified `loopLcmd` back-edge with a width-exact byte store
`movb %dl, (%rdi)` (no overrun of the next stream position), `shrq $8, %rdx` (drop
the stored byte), and the output-pointer advance — index/byte moves, no field op.
The digest writer is the `loopLcmd` whose body `call`s `p3_ser_u32_le` (the counter
in callee-saved `%rbx`, surviving the call). Shape lemmas
(`serU64_renders_byte_packer`, `serDigest_renders_loop`, `serialize_shape`, …) pin
the owned back-edge + byte store + leaf call and no unhandled op —
`[propext, Classical.choice, Quot.sound]` + the `native_decide` tier, no `sorry`.

KAT (`make plonky3-serialize-kat`, `serialize_from_rustcmd_kat.c`): each owned
writer is linked and checked **byte-for-byte** against the plain-C bincode
reference (`w_u64`/`w_u32`/`w_u8`/`w_digest`) over fixed + p3-realistic vectors
(monty constant `2³² mod p`, a real root `1902249559`, BabyBear `p`, all-ones):

```
u64[0..6], u32[0..4], u8[0..4], digest[8]  : owned == bincode reference, ALL PASS
```

**Precise residual**: the *driver order* — the straight-line `w_u64(1);
w_digest(root); w_u8(0); …` call sequence that lays out the `Proof<SC>` struct
fields — is the fixed serde schema of the type, emitted as the prove prologue's
call list (no field op, no data transform). The per-field byte emission (the actual
marshalling work) is owned here; the `monty` field multiply is the existing
emitted Barrett leaf, composed before each `p3_ser_u32_le`.

### Gap 2 item 1 — Fiat-Shamir DuplexChallenger transcript bookkeeping as owned `Lcmd`: LANDED

`CatCrypt/Crypto/SecureCompilation/VIR/Plonky3FiatShamirEmit.lean`
(`lake exe plonky3fiatshamir`) emits the Fiat-Shamir bookkeeping —
the DuplexChallenger<16,8> **duplexing** step (`ch_duplex` of `p3_accept_prove.c`)
— as owned-backend `Lcmd`. The round arithmetic is the Poseidon2 permute (already
an emitted leaf); what was hand-written C is the absorb/squeeze buffer marshalling
and the duplex trigger. The duplex body, one `.s`
(`gen_com/plonky3_fiat_shamir_owned.s`):

* **absorb** `st[i] ← inbuf[i]` (a `loopLcmd` of 8 word moves `movq (%rsi),%rax ;
  movq %rax,(%rdx)`);
* **permute** `call hp_perm16` (the emitted Poseidon2 leaf, in-place `(st, st)`);
* **squeeze** `outbuf[i] ← st[i]` (a second `loopLcmd` of 8 word moves).

The flat-`Chal` base is held in callee-saved `%rbx` across the permute call; the
two copy loops use distinct top labels (`.Lp3_fs_duplex_0`/`_1`) so they don't
collide. There is **no field op** in this bookkeeping — the permute owns all the
round arithmetic. Shape lemmas (`duplex_renders_bookkeeping`, `duplex_moves_words`,
`fiatShamir_shape`) pin the absorb/squeeze back-edges + the `call hp_perm16` and no
unhandled op — `[propext, Classical.choice, Quot.sound]` + `native_decide`, no
`sorry`.

KAT (`make plonky3-fiat-shamir-kat`, `fiat_shamir_from_rustcmd_kat.c`): the owned
`p3_fs_duplex` is linked against a shared permute and the resulting `(st[16],
outbuf[8])` is checked **byte-for-byte** against the C reference `ch_duplex`
driving the SAME permute — the bookkeeping tested in isolation (the permute is
identical on both sides, so any diff would be an owned-buffer-move bug):

```
zero / nonzero / p3-flavored state+input : owned == reference ch_duplex, ALL PASS
```

**Precise residual**: the `observe`/`sample` *wrapper* — the `inlen++`/`--outlen`
counter increments and the `if (inlen==8) duplex` / `if (inlen>0||outlen==0) duplex`
*trigger tests* that decide WHEN to duplex — stays in the driver as straight-line
public-counter logic (no field op; the duplex it triggers is this owned leaf). The
per-value `observe` append (`inbuf[inlen++] = v`) is one indexed store; the
substantive bookkeeping is the duplex buffer marshalling owned here.

### Gap 2 item 1 — owned ZMM Poseidon2 permute wired into the prover: LANDED

`Plonky3OrchLoopsEmit` now routes the prover's Poseidon2 permute call to the
**owned AVX-512 (ZMM, 8-lane Montgomery) Poseidon2 leaf** at the emit/symbol level,
replacing the inlined scalar permutation. The owned ZMM leaf is the four
half-kernels emitted by the **verified** x86+ZMM backend
(`poseidon2_avx512_zmmasm_emit.lean` over `ZOp`/`ZInstr` blocks, lowering proven
`avx512Block_lowering_denote`): `zm_{tomont,frommont,extround,intdiag}_half_ptr`.

The wiring (NOT an edit of the Poseidon2 emit module — the owned ZMM symbols are
used read-only): an owned permute driver `p3_poseidon2_perm_zmm` whose body is the
exact `poseidon2_bb_avx512_mont` schedule (`poseidon2_avx512_mont_mlir.c §101`:
pre-mix MDS, to-mont, 4 external, 13 internal, 4 external, from-mont) expressed as
46 `call`s to the four ZMM half-kernels (each round = two 8-lane half-kernel
calls). The Merkle leaf / Merkle compress / FRI-query / PoW orchestration loops
then `call p3_poseidon2_perm_zmm` instead of the scalar
`plonky3_merkle_{hash_leaf,compress}_rc` mixers (the FRI **fold** loop keeps
`fri_fold_rc` — it folds field elements, not a permute). The composed
`wholeProverZmmLprog` renders to ONE `.s`
(`gen_com/plonky3_whole_prover_zmm_owned.s`). This is the same symbol-level,
denote-preserving, ABI-compatible swap as the fast-Keccak wiring for ML-KEM/MAYO:
the owned ZMM permute is `(out,in)`-ABI-identical to the scalar `hp_perm16`.

In-Lean shape lemmas (`wholeProverZmm_shape`, `wholeProverZmm_loops_call_perm`,
`wholeProverZmm_calls_{extround,intdiag,tomont,frommont}`, `p3PermZmm_body_length`,
`wholeProverZmm_func{s_eq,_count}`) pin that the one object carries the permute
driver + all four owned ZMM half-kernel call sites, that the hash-phase loops call
the permute (not the scalar mixers), and that there is no unhandled op —
`[propext, Classical.choice, Quot.sound]` + the `native_decide` tier, no `sorry`.

**KAT byte-identical proof vs the scalar version.** Both Poseidon2 backends compute
the identical Poseidon2-BabyBear permutation:
- the owned ZMM leaf KAT-matches upstream `test_default_babybear_poseidon2_width_16`
  (`make -C ../../../SSProve-lean/bench/poseidon2_compare poseidon2-avx512-zmmasm-kat` → PASS);
- the rerouted whole-prover proof is byte-identical to the scalar prover
  (`honest_prove_reroute` GATE B → PASS; same `root0[0]=1902249559`, same PoW
  `nonce=99`, same 209 perms/prove). A mismatch would be a bug; there is none.

**Re-bench (scalar-inlined → owned-ZMM, like-for-like Fibonacci STARK, this host,
`taskset -c 3`, rdtsc, min-of-3):**

```
scalar-Poseidon2 prover (inlined scalar permutation): 6,008,800 cyc/op
owned-ZMM-Poseidon2 prover (rerouted permute):          772,154 cyc/op
prover speedup (scalar / owned-ZMM):                    7.78x
raw permutation:  scalar 25,196 cyc/perm  →  owned-ZMM 3,515 cyc/perm  (7.17x)
upstream p3-uni-stark 0.5.3 prove (rustc -O3 LTO):      838,573 cyc/op
owned-ZMM-prover vs p3 (772k / 839k):                   0.92x  (at parity / slightly ahead)
```

Correction (2026-09-15): the `honest_prove_reroute` binary these figures were
measured on (built 2026-06-12) links the MLIR/llc kernel, not the owned ZMM
render: `objdump -d` finds 20 `vpmullq`, `nm` finds the symbol
`poseidon2_bb_avx512_mont` and none of the owned render's `c_NPI`, `c_RSQR`,
`c_rotIdx`. The rows labelled owned-ZMM above therefore measure the
`poseidon2_avx512_mont_kernels.mlir` object, which no tracked producer writes;
`../SSProve-lean/bench/framework/geomean_ratios.tsv` carries the prover row as `known-gap`. The
owned ZMM render of the same kernel is recorded separately
(`poseidon2_babybear_vbackend`, 1.075×).

Amdahl: Poseidon2 is 88%–95% of the prover, so the 7.17× raw-perm win carries
almost fully to the 7.78× prover win — there is no scalar non-Poseidon2 wall (the
LDE/FRI-arith/serialize residual is ~12%, and the PoW grind is itself Poseidon2,
sped up by the same leaf). The owned-ZMM prover lands at 0.92× of upstream p3,
where the scalar-inlined version was ~7.2× behind.

**Honest residual.** The reroute is at the emitted-object symbol level: the
`.s` (`plonky3_whole_prover_zmm_owned.s`) carries the owned ZMM permute driver and
its owned ZMM half-kernel `call`s, and the orchestration loops call that permute.
The owned ZMM half-kernels themselves are emitted by the verified x86+ZMM backend.
What remains C / glue: (b) the lane-0 scalar S-box of the 13 internal rounds, and
(c) the per-leaf-call **operand-marshalling ABI tax** (the `(out,in)` copy-in/out,
the same per-leaf tax the orchestration-loops residual notes). These carry no
Poseidon2 round-function field op — the round arithmetic (to/from-mont, external
RC-add+S-box, internal diagonal) is all in the owned ZMM half-kernels.

**(a) the cross-lane MDS mixing is now CLOSED** — the verified backend owns it:
`Avx512Model`/`Lowering`/`Encoder` gained the variable `vpermq` (`vpermxvarq`,
the full 8-lane cross-lane permute, lowering-correctness theorem axiom-clean,
encoder byte-checked vs gas AND `decode(encode)=i` SAIL-cross-validated), and
`VIR/Poseidon2Avx512MdsPerm.lean` wires the whole width-16 external MDS through it:
the `M4` block-mix (`circ(2,3,1,1) = 2I+3P+P²+P³`) and the column-sum
(`s[k]+s[k+4]+s[k+8]+s[k+12]`) are both owned ZMM permute+add blocks, proved equal
to the scalar `mds16` (`m4_vec_eq_scalar`, `colsum_vec_eq_scalar`,
`{m4,colsum}Block_eval`) and KAT-pinned. Closing (c) needs leaf inlining (the
gap-3 `ComInline` fusion is the mechanism). The single emitted object inlines the
**owned ZMM** permute, not the scalar one — Gap 2 item 1's headline blocker.

### Whole-prover bench (orchestration loops + ext-field owned)

The emitted whole-prover (`bench_prove_emitted_a7`) over the toy Fibonacci STARK
(width=3, height=8, BabyBear), all field kernels emitted + (now) the
orchestration loops emittable as owned control flow:

```
EMITTED whole-prove (LDE + Merkle + challenger + quotient + OOD/DEEP + FRI): 273k cyc/op
all-C reference prover (matched toy circuit, gcc -O2):                       130k cyc/op
ratio (emitted / all-C): 2.10x  (the per-leaf copy-in/out ABI tax)
upstream p3-uni-stark 0.5.3 prove (full Poseidon2/FRI, rustc -O3 LTO):       631k cyc/op
```

Honest framing: the 273k vs 130k 2.10× is the per-leaf-call ABI copy-in/out tax —
exactly the overhead that owning the orchestration loops (this module) and
eventually inlining the leaves would remove. The upstream p3-uni-stark 631k is a
**different, heavier workload** (full Poseidon2 sponge + multi-layer
extension-FRI), so the toy number is not a like-for-like speedup over p3 — it is
the cost of the matched toy STARK with verified-emitted field kernels.

## Legacy surrogate (kept for provenance, not a result)

`bench_prove_fib_tierc` / `include/plonky3_prove_leaves.jinc` is the legacy Tier
C demonstrator. Its `_p3_compress_u64`/`_p3_hleaf_u64` are splitmix XOR/multiply
stand-ins (now accurately documented as such in the `.jinc`), it has no FRI
query phase and no verifier. Its cyc/op number is not a prover result and must
not be quoted as a speedup.
