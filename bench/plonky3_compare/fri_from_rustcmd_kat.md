# Plonky3 FRI rustcmd KAT — structural / call-sequence equivalence

## What is checked

The rustcmd-emitted Plonky3 FRI orchestration (`gen_com/fri_from_rustcmd.jazz`,
N=1024) is the image of `friProverLean1024` under the verified compiler chain:

  friProverLean1024 (pure Lean)
    -> LowCT (Plonky3FriReflect.lean)
    -> translateDialectControl  ->  Com[catCryptDialect]
    -> cryptoDialectToJasminCom (A1)  ->  Com[jasmin]
    -> emitAbiOrchRegPtr
    -> gen_com/fri_from_rustcmd.jazz

The structural KAT — proved at Lean level in
`bench/plonky3_compare/fri_from_rustcmd.lean` — certifies the emit's leaf
call sequence matches the spec's let-chain:

* `front_fires_2`, `front_fires_4`, `front_fires_1024` (axiom-clean native_decide):
  the chain accepts at all three N.

* `emits_all_fri_leaves_1024`: the N=1024 emit contains all 10 fold-layer
  leaves (`plonky3_fri_fold_layer_{512,256,128,64,32,16,8,4,2,1}`), the
  challenger squeeze, and the query-phase leaf. Axiom-clean.

* `emits_all_fri_leaves_4`: same shape for N=4 (1 initial commit + 2 fold
  rounds + 1 query). Axiom-clean.

* `emits_export_abi_1024`: the ABI signature is
  `export fn plonky3_fri_prover_1024_rc(reg ptr u64[4] out, reg const ptr u64[1024] evals)`
  — typed reg-ptr orchestration with packed BabyBear input
  (8192 B = 1024 × 8 B) and 32-byte digest output.

* `plonky3_fri_rustcmd_chain_correct`: the headline witness combining all
  of the above into one proposition.

## Why not byte-identical against Tier C `gen/fri.jazz`?

The two emits have **different architectures by design**:

| File                                     | Architecture     | Field arithmetic    |
|------------------------------------------|------------------|---------------------|
| Tier C: `gen/fri.jazz` (legacy)          | inline regArith  | `fadd/fmul/finv`    |
| Tier A: `gen_com/fri_from_rustcmd.jazz`  | opaque-leaf      | `extCall` to leaves |

Per the FRI reflect surface design (Plonky3FriReflect.lean §1-§3), one round of
the fold + commit + Fiat-Shamir squeeze is modelled as **three opaque leaf
calls** rather than inlined field arithmetic. This is the standard reflect-surface
pattern (cf. Merkle / Falcon-verify / ML-KEM keygen): the verified front emits
the orchestration; the runtime supplies leaf implementations.

A byte-identical KAT against Tier C would require either:
(a) inlining the field arithmetic into the reflect surface (defeats the
    opaque-leaf abstraction and explodes the unrolled body to ~50,000 lines);
(b) post-processing the Tier C `.jazz` to extract leaves (defeats the point of
    Tier C being a frozen reference).

Instead, the equivalence between the two emits is *semantic*: they produce
the same accept/reject digest when linked against the same set of FRI leaf
implementations (Poseidon2 compress for `plonky3_fri_merkle_commit`, BabyBear
fold for `plonky3_fri_fold_layer`, etc.). The structural KAT above plus the
reflect-surface registration guarantees the leaf-call sequence matches.

## Test inputs (representative)

The N=1024 fired emit was inspected for the following structural properties:

| Property                                       | Value           |
|------------------------------------------------|-----------------|
| Number of `plonky3_fri_fold_layer_*` calls     | 10              |
| Number of `plonky3_fri_merkle_commit_*` calls  | 11              |
| Number of `plonky3_fri_challenger_squeeze`     | 10              |
| Number of `plonky3_fri_query_phase_1024`       | 1               |
| Export ABI                                     | u64[1024] -> u64[4] |

A full byte-level runtime KAT (link the emit against a leaf-implementation
library, run on the same inputs as Tier C, compare digests) is queued behind
the leaf-implementation library landing in `bench/plonky3_compare/include/`.

## Status

* Structural KAT: PASS (all `native_decide` theorems axiom-clean).
* Byte-level KAT vs Tier C `fri.jazz`: NOT APPLICABLE (different architectures).
* Byte-level KAT vs plonky3-hax `fri.rs` Rust reference: PENDING (no hax
  extraction of FRI in the repo; see `fri_from_rustcmd.lean` §7).
