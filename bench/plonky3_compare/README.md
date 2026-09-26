# Plonky3 STARK prover chain — emitted through the verified front (#154)

This directory holds the emit drivers, generated `.jazz`, and KAT crosswalk for
the **full Plonky3 STARK prover chain**, emitted from pure Lean through
CatCrypt's verified front. It is the headline "we emit a full PCS" deliverable,
extending the Poseidon2-BabyBear emit (#100/#138/#147/#152) up the prover stack.

The chain is built bottom-up; each layer ships with a denotation-preservation
theorem and a KAT against the `plonky3-hax` reference (`../../../hax-specs/plonky3-hax/`).

## Layers

| # | Layer | Module | Denotation theorem | Emitted `.jazz` |
|---|-------|--------|--------------------|-----------------|
| 1 | Merkle commitment | `Plonky3MerkleEmit.lean` | `merkleLevel_denotation_preserves` | `gen/merkle_build_root.jazz` |
| 2 | Low-degree extension (coset FFT) | `Plonky3LdeEmit.lean` | `ldeStage_denotation_preserves` | `gen/lde_coset_fft.jazz` |
| 3 | FRI (commit + query) | `Plonky3FriEmit.lean` | `friFoldLayer_denotation_preserves` | `gen/fri.jazz` |
| 4 | AIR constraint evaluator | `Plonky3AirEmit.lean` | `airTransition_denotation_preserves` | `gen/air_eval_fib.jazz` |

Modules live under
`CatCrypt/Crypto/SecureCompilation/VIR/Plonky3*Emit.lean`.

### The lane-map keystone, reused twice

`LaneMap.laneMap_eq_scalarMap` / `laneMapIdx_eq_scalar` (the verified
vectorizer heart) instantiates directly at:

* **Merkle tree levels** — each level is a lane-parallel MAP, one two-to-one
  compress per child pair (lane index = the parent slot);
* **FRI fold** — each fold layer is a lane-parallel MAP over the surviving
  cosets, one `fri_fold` per coset.

The LDE butterfly and the AIR per-step constraint sweep are the same shape. The
denotation theorems are compositions of the keystone, not new theory.

### No opaque leaf

Every layer's field/byte arithmetic is regArith-only (`+ - * & | ^ << >> >>s`,
no `%`-op for the Poseidon2 path; the Baby Bear field reduction uses the same
fold-and-conditional-subtract discipline as `Poseidon2Emit.lean`). The emitted
`.jazz` contains no `extCall` — verified by each module's `*Jazz_shape`
theorem.

## KAT: byte-identity per layer

The reference is the self-contained `plonky3-hax` crate
(`../../../hax-specs/plonky3-hax/src/`), whose own test suite
(`plonky3-hax/tests/kat_vectors.rs`, 33 tests) freezes the regression vectors.
Each Lean module pins the SAME constants via `native_decide`; the byte-identity
holds against one common oracle.

`plonky3_kat.rs` is the human-readable crosswalk: it recomputes each layer's
reference value directly from the plonky3-hax spec functions and prints it
alongside the Lean KAT theorem that pins it. To run it, copy into
`plonky3-hax/examples/` and `cargo run --example plonky3_kat`, or read it
alongside `cargo test --test kat_vectors` (run from `plonky3-hax/`).

| Layer | Lean KAT theorem | plonky3-hax reference | Value |
|-------|------------------|------------------------|-------|
| 1 | `kat_root_four_full` | `merkle::merkle_build_root([H(1)..H(4)],4)` | `00e1d70044a1e330…899b78` (full 32 bytes) |
| 1 | `kat_compress_const_full` | `merkle::hash_two_to_one([1;32],[2;32])` | `b5fd0238a9bdfef8…f51e80` (full 32 bytes) |
| 1 | `kat_leaf_zero_full` | `merkle::hash_field_elem(0)` | `09c4d5a801ac8dd0…9c5d40` (full 32 bytes) |
| 2 | `kat_poly_eval_horner` | `baby_bear::bb_poly_eval([7,11,13,17],3)` | `616` |
| 2 | `kat_domain_element_zero` | `fri::domain_element(8,0)` | `1` |
| 2 | `kat_root_of_unity_order_two` | `baby_bear::bb_root_of_unity(1)` | `p − 1` (the order-2 element) |
| 3 | `kat_fri_fold_specific` | `fri::fri_fold(100,50,7,3)` | `287609503` |
| 3 | `kat_fold_polynomial_linear` | `fri::fold_polynomial([3,5],11)` | `[58]` (= `3 + 11·5 mod p`) |
| 3 | `kat_sibling_index` / `kat_folded_index` | `fri::sibling_index` / `folded_index` | index identities |
| 4 | `kat_fibonacci_trace_values` | `air::fib_trace(10)` col 1 | `[1,1,2,3,5,8,13,21,34,55]` |
| 4 | `kat_air_max_degree` | `air::air_max_degree(fib_air())` | `1` |
| 4 | `kat_fib_trace_satisfies_air` | `air::eval_transition` over `fib_trace` | every constraint `= 0` |

The Merkle KATs pin the **full 32-byte digest** (the airtight byte-identity
claim); the `*_prefix` theorems are lighter 4-byte witnesses kept alongside.

## Axiom budget

Each `*_denotation_preserves` theorem: `[propext, Quot.sound]` (the AIR one
needs only `[Quot.sound]`). The KAT theorems additionally carry the
`native_decide` axioms, as in the Poseidon2 / NTT precedent.

## How far the chain goes

All four layers — Merkle, LDE, FRI, AIR — emit through the verified front with
their denotation theorems and KATs. The AIR demonstrator is the standard
Plonky3-tutorial Fibonacci AIR. What this chain does **not** yet emit as a
single fused `prove()` entry point: the cross-layer wiring (transcript /
Fiat-Shamir, the OOD / DEEP quotient, the proof-of-work grinding) that
`plonky3-hax/src/plonky3.rs::plonky3_prove` orchestrates. Those compose the
four emitted kernels; the per-kernel emits here are the load-bearing
arithmetic. The whole-prover regression oracle is
`plonky3-hax/tests/kat_vectors.rs::kat_plonky3_fib_height{8,16}_*`.

## Whole prover with the EMITTED trace-LDE phase (REV-11 A5)

`bench_prove_emitted.c` (`make plonky3-prove-emitted-rustcmd-bench`) is the
height-8 Fibonacci whole-prover whose **trace-LDE phase runs through the EMITTED
A3 column-LDE leaves** — the 7 register-arith leaves of
`gen_com/lde_column_from_rustcmd.jazz` (`lde_intt8_rc`, `lde_twist_rc`,
`lde_ntt32_l{0..4}_rc`), composed per trace column on a shared 32-word buffer and
interleaved row-major into the LDE buffer — **in place of the hand-written
`.jinc` / C-reference LDE**. Those leaves carry the `allRegArith` /
`leaf.denote = spec` connection proven in
`CatCrypt/Crypto/SecureCompilation/VIR/Plonky3LdeColumnEmit.lean` (every binding
is a `regArith` mul/shr/sub/and/add — the Barrett field mul-mod, no hardware
`%`, no opaque leaf, no `fmul`/`%=P`).

Emitted vs hand-written (honest):

| Phase | Status |
|-------|--------|
| trace-LDE (3 × `computeColumnLde`) | **EMITTED** through the verified front (allRegArith, KAT-witnessed numeric equality to the Lean spec) |
| Merkle commit | hand-written orchestration glue (byte-identical to the Lean spec / `.jinc`; KAT-witnessed, NOT emitted) |
| challenger / Fiat-Shamir squeeze | hand-written glue |
| quotient compose | hand-written glue |
| OOD / DEEP | hand-written glue |
| FRI fold + final FRI commit | hand-written glue (the A4 `fri_fold` leaf is emitted standalone but not yet wired into this orchestration) |
| buffer interleave / plumbing | hand-written glue |

KAT: (1) the emitted trace-LDE phase equals `computeColumnLde` per element;
(2) the **whole-prover proof object** equals the all-C reference prover (whose
`ref_trace_lde` is byte-identical to `computeColumnLde`). The FRI verifier
re-derives the deterministic LDE → commit → α → fold → final-commit chain and
**ACCEPTS** the honest proof, **REJECTS** a tampered trace. The bench reports
whole-prove cyc/op (emitted-LDE prover vs all-C reference). The ~7–8× ratio is
the per-leaf copy-in/out ABI tax of the 7-leaf composition (each leaf
re-materializes its 139-word input table), consistent with the A3/A4 leaf-ABI
findings — not the hand-written `fmul`/`%=P` path.

Residual to re-wire: the Merkle/FRI-fold phases have emitted leaves (A1/A2 + A4)
but are not yet composed into this orchestration; the challenger/quotient/OOD
glue has no emitted leaf yet. Next step: wire the A1/A2 Merkle compress/hash and
the A4 `fri_fold` leaves into the commit and FRI phases (same per-leaf-ABI
composition pattern), leaving only the Fiat-Shamir/quotient/OOD glue
hand-written.

## Whole prover with EMITTED trace-LDE + Merkle commit + FRI fold (REV-11 A6)

`bench_prove_emitted_a6.c` (`make plonky3-prove-emitted-a6-rustcmd-bench`)
extends the A5 driver: the whole-prover now runs **three** phases through the
verified-front EMITTED leaves, linking all four emitted `.s` objects
(`lde_column_*`, `compress_*`, `hash_leaf_*`, `fri_fold_*`):

| Phase | Status (A6) |
|-------|-------------|
| trace-LDE (3 × `computeColumnLde`) | **EMITTED** — A3, 7 coset-NTT column-LDE leaves |
| Merkle commit (32-leaf 5-level tree) | **EMITTED** — A2 leaf-hash ×32 + A1 2-to-1 compress ×31 |
| Fiat-Shamir challenger squeeze | hand-written glue (no emitted leaf yet) |
| quotient compose | hand-written glue (no emitted leaf yet) |
| OOD / DEEP | hand-written glue (no emitted leaf yet) |
| FRI fold + final FRI commit | **EMITTED** — A4 `fri_fold_rc` per fold layer (BabyBear `friFold` with inline Fermat inverse, no hardware `%`) + A1/A2 commit |
| buffer interleave / coset-point / tree plumbing | hand-written glue |

Every wired-in leaf carries the `allRegArith` / `leaf.denote = spec` connection
proven in Lean (`Plonky3CompressEmit.compress_is_regarith_only`,
`Plonky3HashLeafEmit.hash_is_regarith_only`,
`Plonky3LdeColumnEmit` allRegArith, `Plonky3FriFoldEmit.friFold_is_regarith_only`
/ `bbInv_is_regarith_only`). The FRI fold operates on **canonical** field
elements (`% P`), matching the emitted leaf's internal Barrett reduction.

KATs (all PASS): (1) emitted trace-LDE == spec `computeColumnLde` per element;
(2) emitted Merkle commit root == spec Merkle root; (3) emitted `fri_fold_rc` ==
spec `friFold` per element; (4) the **whole-prover proof object** (all three
phases through emitted leaves) == the all-C reference prover (every phase
byte-identical to the Lean spec). The FRI verifier re-derives the deterministic
LDE → commit → α → fold → final-commit chain: honest proof **ACCEPTS**, tampered
trace **REJECTS**.

Bench: whole-prove ~290k cyc/op for the emitted prover vs ~140k for the all-C
reference (~2.1×). The A6 reference uses the same field-correct `friFold` as the
emitted leaf (both run the per-fold Fermat inverse), so the ratio is the
per-leaf copy-in/out ABI tax of the now-three emitted phases — not a
hand-written `fmul`/`%=P` path. (The A5 ~7× figure was against an A5 reference
that used a cheaper non-field fold; A6's reference is heavier, hence the lower
ratio, but both prover and reference are now field-correct.)

**FINAL residual (A6):** EMITTED = trace-LDE (A3) + Merkle commit (A1+A2) +
FRI fold + final FRI commit (A4 + A1/A2). HAND-WRITTEN orchestration glue (no
emitted leaf yet exists for these): Fiat-Shamir challenger squeeze, quotient
compose, OOD/DEEP, and the buffer interleave / coset-point / tree wiring.

## Whole prover with EMITTED challenger + quotient + OOD/DEEP too (REV-11 A7)

`bench_prove_emitted_a7.c` (`make plonky3-prove-emitted-a7-rustcmd-bench`)
extends A6 by emitting the three remaining orchestration-glue computations,
linking a fifth emitted `.s` object (`glue_from_rustcmd.s`, from
`CatCrypt/Crypto/SecureCompilation/VIR/Plonky3GlueEmit.lean`):

| Phase | Status (A7) |
|-------|-------------|
| trace-LDE | **EMITTED** (A3) |
| Merkle commit | **EMITTED** (A1+A2) |
| Fiat-Shamir challenger squeeze | **EMITTED** — A7 `challenger_squeeze_rc` |
| quotient compose | **EMITTED** — A7 `quotient_compose_elem_rc` (per element) |
| OOD / DEEP | **EMITTED** — A7 `ood_deep_elem_rc` (per element) |
| FRI fold + final FRI commit | **EMITTED** (A4 + A1/A2) |
| buffer interleave / coset-point / tree shape | hand-written (NO field arithmetic — pure index plumbing) |

The challenger leaf reproduces the C reference's wrapping-`u64` +
single-subtract semantics exactly: the `acc·C` product wraps mod 2⁶⁴, then a
full `u64 → field` reduction `bbModU64` (32-bit split + Barrett, since the
wrapping product exceeds 2⁶²) brings it back; the digest absorb / accumulate use
the branchless `pr_reduce` csub. The quotient/OOD leaves are kept to
canonical-input Barrett arithmetic — the wrapping `α`-power chain (the
non-canonical `α` is the raw challenger output) is precomputed by the driver in
C as the canonical coefficients `c_k = (k+1)·α^k mod p` / the running `pw`, so
the leaves do only `bbMul`/`bbAdd`/`bbSub` on operands `< p`. Each leaf is
front-compiled (LowCT → `translateDialectControl` →
`cryptoDialectToJasminCom`), pure scalar arith, and denote-gated against the
independent `pr_*` transcription in Lean
(`Plonky3GlueEmit.{chal,quot,ood}_denote_spec` /
`{chal,quot,ood}_is_purearith_only`).

KATs (all PASS): the three emitted glue leaves vs `ref_challenger_squeeze` /
`ref_quotient_compose` / `ref_ood_deep` per element (`glue_from_rustcmd_kat.c`),
plus the **whole-prover proof object** with ALL of trace-LDE + Merkle +
challenger + quotient + OOD/DEEP + FRI fold through emitted leaves == the all-C
reference prover. FRI verifier: honest **ACCEPTS**, tampered **REJECTS**. Bench:
whole-prove ~293k cyc/op emitted vs ~140k all-C (~2.1× per-leaf copy-in/out ABI
tax).

**FINAL residual (A7):** every field-arithmetic phase of the prover —
trace-LDE, Merkle commit, challenger squeeze, quotient compose, OOD/DEEP, FRI
fold + final commit — is now EMITTED through the verified front with
`leaf.denote = spec` by construction. The only hand-written residual is the
**non-arithmetic orchestration plumbing**: the loops that gather operands,
select coset points, accumulate the per-layer/per-element `α`-powers, interleave
buffers, and shape the Merkle trees. These carry NO `bb*` field operation — they
are array indexing and control flow that route inputs into the emitted leaves
(the kind of data-dependent indexing the regArith straight-line path does not
express; it would need the `toJasminCmd` array+loop path).

## FRI proof object + verifier (emit -> accept; tamper -> reject)

`include/plonky3_fri_proof_leaves.jinc` (`plonky3_fri_prove_obj`, exported via
`gen_com/fri_proof_from_rustcmd_link.jazz` as `plonky3_fri_prove_obj_rc`) emits
a **real structured FRI proof object** rather than the digest-only collapse of
the prove orchestration's `plonky3_fri_prove_8`. The proof matches the
`plonky3-hax/src/fri.rs` shape (`FriProof` / `FriLayer` / `FriLayerQuery` +
`fri_prove_column`): per-layer Merkle commitments of the folded codewords,
per-query openings (eval_pos + eval_neg + Merkle authentication paths at the
Fiat-Shamir query indices), and the final-layer remainder polynomial.

The fold uses the **true degree-halving formula** of `fri.rs::fri_fold`
`p'(x^2) = (p(x)+p(-x))/2 + alpha*(p(x)-p(-x))/(2x)` (NOT the
`(a+b)+alpha*(a-b)` surrogate of the digest path).

Parameters: single column, n=32 (domain_log2=5), 4 fold layers (32->16->8->4->2),
3 queries, coset_shift=1; remainder is degree 1.

`bench_fri_proof_from_rustcmd.c` is the **external KAT** (the conform.c
pattern): it runs the emitted prover on a known low-degree column LDE, then a
spec-adherent C verifier (`fri_verify`, mirroring `fri.rs::fri_verify` — Merkle
path checks + the fold-consistency relation across layers + the remainder
low-degree check). The honest proof must **ACCEPT**; four tampered proofs
(corrupted eval, corrupted Merkle path, corrupted remainder, wrong fold
challenge) must **REJECT**. The harness reports prove and verify cyc/op.

```
make plonky3-fri-proof-rustcmd-bench
```

The Merkle hash is the same u64-lane `_p3_hleaf_u64` / `_p3_compress_u64` the
trace commitment uses (the CatCrypt bridge axiomatizes it as a random oracle;
prover and verifier agree on the concrete mixing).

## Bench (queued)

Per-layer cyc/op vs Plonky3 native requires a local Plonky3 build with
per-kernel benches. As with the `mlkem_ntt_4way` precedent (libcrux NTT prims
are `pub(crate)`, no per-op bench without a patch), upstream Plonky3 does not
expose the Merkle/LDE/FRI/AIR kernels as standalone benchable entry points.
Bench is therefore **queued**: the emitted `.jazz` is the artifact of record;
the structural + KAT layer (hash/field/polynomial arithmetic) is fully tested.
No fabricated bench numbers.

## Regenerate

```
lake env lean bench/plonky3_compare/plonky3_emit.lean
```

writes the four `.jazz` files into `gen/`.
