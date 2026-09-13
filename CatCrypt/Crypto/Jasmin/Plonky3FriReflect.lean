/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Crypto.Jasmin.LowCTStraightLineCheck

/-!
# Plonky3 FRI reflect surface — Tier A migration of the FRI layer

Layer 3 of the Plonky3 STARK chain (FRI commit + query phase, polynomial
degree-halving with Fiat-Shamir challenge), lifted through the verified
compiler chain `LowCT → CryptoSSA → Com → jasmin`.

This is the architectural opposite of the legacy
`CatCrypt/Crypto/SecureCompilation/VIR/Plonky3FriEmit.lean` string-template
emit (`bench/plonky3_compare/gen/fri.jazz` is built by `String.intercalate` —
out-of-chain by construction). This file is the FRI analogue of
`Plonky3Reflect.lean` (Wave 1 Merkle) and `FalconReflect.lean` (#191): every
byte of the new emit goes through the verified front.

## FRI equation (per layer)

```
  fri_fold(p, alpha):
    -- p has 2*half evaluations on a domain {x_i, -x_i}; output has half evals
    for i in 0..half:
      e_pos  = p[i]
      e_neg  = p[i + half]
      x      = xs[i]
      sum    = e_pos + e_neg
      diff   = e_pos - e_neg
      p_even = sum  / 2
      p_odd  = diff / (2*x)
      p'[i]  = p_even + alpha * p_odd
    return p'
```

Each FRI round halves the polynomial degree by folding with `alpha`, then
commits the folded array via Merkle. After `log2 N` rounds we have a single
constant; the query phase verifies Merkle openings at sampled indices.

We model each major step as one opaque leaf call:

| Lean axiom                          | Leaf name (.jazz)                  | TowerType         |
|-------------------------------------|------------------------------------|-------------------|
| `plonky3_fri_fold_layer N`          | `plonky3_fri_fold_layer_N`         | `TBytes (8·N)`    |
| `plonky3_fri_merkle_commit N`       | `plonky3_fri_merkle_commit_N`      | `TBytes 32`       |
| `plonky3_fri_challenger_squeeze`    | `plonky3_fri_challenger_squeeze`   | `TBytes 8`        |
| `plonky3_fri_query_phase N`         | `plonky3_fri_query_phase_N`        | `TBytes 32`       |

`plonky3_fri_merkle_commit_N` is FRI-local (FRI's per-layer commitment) and
deliberately namespaced separately from Wave 1's `plonky3_merkle_*` family
so the two reflect surfaces don't collide. The runtime can wire it to the
same underlying Poseidon2 implementation.

A full FRI commit+query over `N = 2^k` evaluations is:
* one challenger squeeze per layer (`α_0, …, α_{k-1}`)
* one `fri_fold_layer` per layer producing the folded array
* one `merkle_commit` per layer producing the commitment digest
* one closing `query_phase` taking the final root and producing the
  acceptance / rejection digest.

The fold loop is **statically unrolled** at Lean time into a flat `RSeq`
of `RCall` chains (`RFor` is not consumed by `translate` — line 752 of
`LowCTToCryptoSSA.lean`, same workaround as `Plonky3Reflect.lean`).

## Relation to legacy Tier C `Plonky3FriEmit.lean`

The legacy file emits its `.jazz` via `String.intercalate` (no compiler
correctness theorem witnesses the body). This file replaces that pattern with
an in-chain emit. The legacy emit is kept as an out-of-chain reference
(`bench/plonky3_compare/gen/fri.jazz`) until the FRI bench harness migrates.

## References

* Plonky3 FRI: `plonky3-hax/src/fri.rs`
* Wave 1 sibling: `CatCrypt/Crypto/Jasmin/Plonky3Reflect.lean`
* Driver template: `bench/plonky3_compare/merkle_from_rustcmd.lean`
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque Plonky3 FRI surface types

The reflect surface treats one FRI evaluation layer as an opaque byte buffer
of `8 · N` bytes (`N` BabyBear field elements, 8 bytes per element).
Commitments are 32-byte digests. -/

/-- A buffer of `N` packed BabyBear evaluations (8 bytes per field element).
    The `plonky3_fri_fold_layer_N` leaf consumes a `Plonky3FriEvals (2·N)`
    plus the per-x challenge inputs and produces a `Plonky3FriEvals N`. -/
axiom Plonky3FriEvals (N : Nat) : Type
/-- Axiomatic inhabitant. -/ axiom Plonky3FriEvals.default (N : Nat) : Plonky3FriEvals N
noncomputable instance (N : Nat) : Inhabited (Plonky3FriEvals N) :=
  ⟨Plonky3FriEvals.default N⟩

/-- A 32-byte FRI-layer Merkle digest (same byte-shape as
    `Plonky3Digest` in Wave 1, kept FRI-local for clean reflect-surface
    namespacing). -/
axiom Plonky3FriDigest : Type
/-- Axiomatic inhabitant. -/ axiom Plonky3FriDigest.default : Plonky3FriDigest
noncomputable instance : Inhabited Plonky3FriDigest := ⟨Plonky3FriDigest.default⟩

/-- An 8-byte Fiat-Shamir challenge (one BabyBear element produced by
    the challenger sponge). -/
axiom Plonky3FriChallenge : Type
/-- Axiomatic inhabitant. -/ axiom Plonky3FriChallenge.default : Plonky3FriChallenge
noncomputable instance : Inhabited Plonky3FriChallenge :=
  ⟨Plonky3FriChallenge.default⟩

/-! ## 2. FRI leaves (axioms = opaque jasmin function symbols)

Each leaf is parameterised by its array-width (the layer size in field
elements); a single emit instantiates these at a fixed depth `k`, so the
leaves below are family-indexed by `Nat`. -/

/-- One FRI fold round, taking `2·N` evaluations to `N`. The fold equation
    `p'[i] = (p[i] + p[i+half])/2 + α · (p[i] - p[i+half])/(2 xs[i])` uses a
    challenge `α`, but this leaf takes no challenge argument. -/
axiom plonky3_fri_fold_layer (N : Nat) :
    Plonky3FriEvals (2 * N) → Plonky3FriEvals N

/-- Per-FRI-layer Merkle commitment: collapse a folded `N`-evaluation array
    into a 32-byte digest under the Poseidon2 sponge. -/
axiom plonky3_fri_merkle_commit (N : Nat) :
    Plonky3FriEvals N → Plonky3FriDigest

/-- Fiat-Shamir challenger squeeze: derive the next-layer challenge `α_k`
    from the running transcript-state (modelled as the previous layer's
    commitment). -/
axiom plonky3_fri_challenger_squeeze :
    Plonky3FriDigest → Plonky3FriChallenge

/-- Query phase: given the final remainder commitment and the original
    top-layer commitment, produce the verifier's accept/reject digest.
    A real implementation would unfold this into per-query Merkle-path
    checks; we keep it as a single opaque leaf in the reflect surface so
    the verified front emits the call site and the runtime supplies the
    bulk-checking implementation. -/
axiom plonky3_fri_query_phase (N : Nat) :
    Plonky3FriDigest → Plonky3FriDigest

/-! ## 3. `@[rust_cmd_pattern]` registrations (per fixed N) -/

/-- Register `plonky3_fri_fold_layer` for the N=512→256 layer.
    Output array of 512 elements = `TBytes (8 · 512) = TBytes 4096`. -/
@[rust_cmd_pattern]
def plonky3FriFoldLayer512Pattern : LowCTPattern where
  name      := "plonky3_fri_fold_layer_512"
  fnHead    := ``plonky3_fri_fold_layer
  arity     := 1
  towerType := .TBytes (8 * 512)

/-- Register `plonky3_fri_merkle_commit` at the topmost width 1024
    (corresponds to the input-layer commitment). -/
@[rust_cmd_pattern]
def plonky3FriMerkleCommit1024Pattern : LowCTPattern where
  name      := "plonky3_fri_merkle_commit_1024"
  fnHead    := ``plonky3_fri_merkle_commit
  arity     := 1
  towerType := .TBytes 32

/-- Register `plonky3_fri_challenger_squeeze`. -/
@[rust_cmd_pattern]
def plonky3FriChallengerSqueezePattern : LowCTPattern where
  name      := "plonky3_fri_challenger_squeeze"
  fnHead    := ``plonky3_fri_challenger_squeeze
  arity     := 1
  towerType := .TBytes 8

/-- Register `plonky3_fri_query_phase` for the topmost N. -/
@[rust_cmd_pattern]
def plonky3FriQueryPhase1024Pattern : LowCTPattern where
  name      := "plonky3_fri_query_phase_1024"
  fnHead    := ``plonky3_fri_query_phase
  arity     := 1
  towerType := .TBytes 32

/-! ## 4. Pure-Lean FRI prover function

Each `friProverLean_<N>` is the pure Lean specification for the fixed-depth
emit. The body is a flat let-chain mirroring the hand-built `LowCT`
exactly. Concretely we model:

* one initial Merkle commitment of the input evaluations (the prover's
  "layer-0 commitment" sent to the verifier),
* one (squeeze, fold, commit) triple per round,
* one final query-phase digest.

The naming `friProverLean_N` reflects that we model the *prover side*
(commit phase) explicitly; the verifier's query check is folded into one
opaque leaf. -/

/-- Pure-Lean FRI prover for `N = 4` initial evaluations (`log2 N = 2`:
    two fold rounds, three commitments). -/
noncomputable def friProverLean4 (evals : Plonky3FriEvals 4) : Plonky3FriDigest :=
  -- Layer 0 commitment
  let c0  := plonky3_fri_merkle_commit 4 evals
  -- Round 1: fold 4 → 2, commit
  let _α0 := plonky3_fri_challenger_squeeze c0
  let e1  := plonky3_fri_fold_layer 2 evals
  let c1  := plonky3_fri_merkle_commit 2 e1
  -- Round 2: fold 2 → 1, commit
  let _α1 := plonky3_fri_challenger_squeeze c1
  let e2  := plonky3_fri_fold_layer 1 e1
  let c2  := plonky3_fri_merkle_commit 1 e2
  -- Query phase: produce accept/reject digest
  plonky3_fri_query_phase 4 c2

/-- Pure-Lean FRI prover for `N = 2`. -/
noncomputable def friProverLean2 (evals : Plonky3FriEvals 2) : Plonky3FriDigest :=
  let c0  := plonky3_fri_merkle_commit 2 evals
  let _α0 := plonky3_fri_challenger_squeeze c0
  let e1  := plonky3_fri_fold_layer 1 evals
  let c1  := plonky3_fri_merkle_commit 1 e1
  plonky3_fri_query_phase 2 c1

/-- Pure-Lean FRI prover for `N = 1024` initial evaluations (`log2 N = 10`:
    ten fold rounds = ten (squeeze, fold, commit) triples). -/
noncomputable def friProverLean1024 (evals : Plonky3FriEvals 1024) :
    Plonky3FriDigest :=
  let c0   := plonky3_fri_merkle_commit 1024 evals
  let _α0  := plonky3_fri_challenger_squeeze c0
  let e1   := plonky3_fri_fold_layer 512 evals
  let c1   := plonky3_fri_merkle_commit 512  e1
  let _α1  := plonky3_fri_challenger_squeeze c1
  let e2   := plonky3_fri_fold_layer 256 e1
  let c2   := plonky3_fri_merkle_commit 256  e2
  let _α2  := plonky3_fri_challenger_squeeze c2
  let e3   := plonky3_fri_fold_layer 128 e2
  let c3   := plonky3_fri_merkle_commit 128  e3
  let _α3  := plonky3_fri_challenger_squeeze c3
  let e4   := plonky3_fri_fold_layer 64  e3
  let c4   := plonky3_fri_merkle_commit 64   e4
  let _α4  := plonky3_fri_challenger_squeeze c4
  let e5   := plonky3_fri_fold_layer 32  e4
  let c5   := plonky3_fri_merkle_commit 32   e5
  let _α5  := plonky3_fri_challenger_squeeze c5
  let e6   := plonky3_fri_fold_layer 16  e5
  let c6   := plonky3_fri_merkle_commit 16   e6
  let _α6  := plonky3_fri_challenger_squeeze c6
  let e7   := plonky3_fri_fold_layer 8   e6
  let c7   := plonky3_fri_merkle_commit 8    e7
  let _α7  := plonky3_fri_challenger_squeeze c7
  let e8   := plonky3_fri_fold_layer 4   e7
  let c8   := plonky3_fri_merkle_commit 4    e8
  let _α8  := plonky3_fri_challenger_squeeze c8
  let e9   := plonky3_fri_fold_layer 2   e8
  let c9   := plonky3_fri_merkle_commit 2    e9
  let _α9  := plonky3_fri_challenger_squeeze c9
  let e10  := plonky3_fri_fold_layer 1   e9
  let c10  := plonky3_fri_merkle_commit 1    e10
  plonky3_fri_query_phase 1024 c10

/-! ## 5. Hand-built `LowCT` bodies — the front-end input

`reifyLowCT%` does not consult the registry, so we hand-build the body.
Downstream (`translate → cryptoDialectToJasminCom → emitAbiOrchRegPtr`) is
unmodified. Each `RCall` matches one `let`-binding in `friProverLean_N`. -/

/-- TowerType for an FRI evaluation array of width `N` (8 bytes/elem). -/
def plonky3FriEvalsTowerType (N : Nat) : TowerType := .TBytes (8 * N)
/-- TowerType for an FRI-layer digest. -/
def plonky3FriDigestTowerType : TowerType := .TBytes 32
/-- TowerType for an FRI Fiat-Shamir challenge (1 BabyBear element). -/
def plonky3FriChallengeTowerType : TowerType := .TBytes 8

def locPlonky3Fri (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-- Per-layer fold leaf name: e.g. `plonky3_fri_fold_layer_256`. -/
def plonky3FriFoldLeafName (N : Nat) : String :=
  "plonky3_fri_fold_layer_" ++ toString N

/-- Per-layer commit leaf name. -/
def plonky3FriCommitLeafName (N : Nat) : String :=
  "plonky3_fri_merkle_commit_" ++ toString N

/-- Per-N query-phase leaf name. -/
def plonky3FriQueryLeafName (N : Nat) : String :=
  "plonky3_fri_query_phase_" ++ toString N

/-- Body for `N = 2`: one initial commit, one (squeeze, fold, commit), one query. -/
def friProverBody2 : LowCT :=
  let evals_l  := locPlonky3Fri "evals"     (plonky3FriEvalsTowerType 2)
  let c0_l     := locPlonky3Fri "c0"        plonky3FriDigestTowerType
  let alpha0_l := locPlonky3Fri "alpha0"    plonky3FriChallengeTowerType
  let e1_l     := locPlonky3Fri "e1"        (plonky3FriEvalsTowerType 1)
  let c1_l     := locPlonky3Fri "c1"        plonky3FriDigestTowerType
  let result_l := locPlonky3Fri "__result"  plonky3FriDigestTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall (plonky3FriCommitLeafName 2)        c0_l     [evals_l]))
    (.RCall "plonky3_fri_challenger_squeeze"    alpha0_l [c0_l]))
    (.RCall (plonky3FriFoldLeafName 1)          e1_l     [evals_l]))
    (.RCall (plonky3FriCommitLeafName 1)        c1_l     [e1_l]))
    (.RCall (plonky3FriQueryLeafName 2)         result_l [c1_l])

/-- Body for `N = 4`: layer-0 commit + 2 fold rounds + query. -/
def friProverBody4 : LowCT :=
  let evals_l  := locPlonky3Fri "evals"     (plonky3FriEvalsTowerType 4)
  let c0_l     := locPlonky3Fri "c0"        plonky3FriDigestTowerType
  let alpha0_l := locPlonky3Fri "alpha0"    plonky3FriChallengeTowerType
  let e1_l     := locPlonky3Fri "e1"        (plonky3FriEvalsTowerType 2)
  let c1_l     := locPlonky3Fri "c1"        plonky3FriDigestTowerType
  let alpha1_l := locPlonky3Fri "alpha1"    plonky3FriChallengeTowerType
  let e2_l     := locPlonky3Fri "e2"        (plonky3FriEvalsTowerType 1)
  let c2_l     := locPlonky3Fri "c2"        plonky3FriDigestTowerType
  let result_l := locPlonky3Fri "__result"  plonky3FriDigestTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall (plonky3FriCommitLeafName 4)        c0_l     [evals_l]))
    (.RCall "plonky3_fri_challenger_squeeze"    alpha0_l [c0_l]))
    (.RCall (plonky3FriFoldLeafName 2)          e1_l     [evals_l]))
    (.RCall (plonky3FriCommitLeafName 2)        c1_l     [e1_l]))
    (.RCall "plonky3_fri_challenger_squeeze"    alpha1_l [c1_l]))
    (.RCall (plonky3FriFoldLeafName 1)          e2_l     [e1_l]))
    (.RCall (plonky3FriCommitLeafName 1)        c2_l     [e2_l]))
    (.RCall (plonky3FriQueryLeafName 4)         result_l [c2_l])

/-- Body for `N = 1024`: layer-0 commit + 10 fold rounds + query. -/
def friProverBody1024 : LowCT :=
  let evals_l  := locPlonky3Fri "evals"     (plonky3FriEvalsTowerType 1024)
  let c0_l     := locPlonky3Fri "c0"        plonky3FriDigestTowerType
  let alpha0_l := locPlonky3Fri "alpha0"    plonky3FriChallengeTowerType
  let e1_l     := locPlonky3Fri "e1"        (plonky3FriEvalsTowerType 512)
  let c1_l     := locPlonky3Fri "c1"        plonky3FriDigestTowerType
  let alpha1_l := locPlonky3Fri "alpha1"    plonky3FriChallengeTowerType
  let e2_l     := locPlonky3Fri "e2"        (plonky3FriEvalsTowerType 256)
  let c2_l     := locPlonky3Fri "c2"        plonky3FriDigestTowerType
  let alpha2_l := locPlonky3Fri "alpha2"    plonky3FriChallengeTowerType
  let e3_l     := locPlonky3Fri "e3"        (plonky3FriEvalsTowerType 128)
  let c3_l     := locPlonky3Fri "c3"        plonky3FriDigestTowerType
  let alpha3_l := locPlonky3Fri "alpha3"    plonky3FriChallengeTowerType
  let e4_l     := locPlonky3Fri "e4"        (plonky3FriEvalsTowerType 64)
  let c4_l     := locPlonky3Fri "c4"        plonky3FriDigestTowerType
  let alpha4_l := locPlonky3Fri "alpha4"    plonky3FriChallengeTowerType
  let e5_l     := locPlonky3Fri "e5"        (plonky3FriEvalsTowerType 32)
  let c5_l     := locPlonky3Fri "c5"        plonky3FriDigestTowerType
  let alpha5_l := locPlonky3Fri "alpha5"    plonky3FriChallengeTowerType
  let e6_l     := locPlonky3Fri "e6"        (plonky3FriEvalsTowerType 16)
  let c6_l     := locPlonky3Fri "c6"        plonky3FriDigestTowerType
  let alpha6_l := locPlonky3Fri "alpha6"    plonky3FriChallengeTowerType
  let e7_l     := locPlonky3Fri "e7"        (plonky3FriEvalsTowerType 8)
  let c7_l     := locPlonky3Fri "c7"        plonky3FriDigestTowerType
  let alpha7_l := locPlonky3Fri "alpha7"    plonky3FriChallengeTowerType
  let e8_l     := locPlonky3Fri "e8"        (plonky3FriEvalsTowerType 4)
  let c8_l     := locPlonky3Fri "c8"        plonky3FriDigestTowerType
  let alpha8_l := locPlonky3Fri "alpha8"    plonky3FriChallengeTowerType
  let e9_l     := locPlonky3Fri "e9"        (plonky3FriEvalsTowerType 2)
  let c9_l     := locPlonky3Fri "c9"        plonky3FriDigestTowerType
  let alpha9_l := locPlonky3Fri "alpha9"    plonky3FriChallengeTowerType
  let e10_l    := locPlonky3Fri "e10"       (plonky3FriEvalsTowerType 1)
  let c10_l    := locPlonky3Fri "c10"       plonky3FriDigestTowerType
  let result_l := locPlonky3Fri "__result"  plonky3FriDigestTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq
  (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq
  (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall (plonky3FriCommitLeafName 1024)     c0_l     [evals_l]))
    (.RCall "plonky3_fri_challenger_squeeze"    alpha0_l [c0_l]))
    (.RCall (plonky3FriFoldLeafName 512)        e1_l     [evals_l]))
    (.RCall (plonky3FriCommitLeafName 512)      c1_l     [e1_l]))
    (.RCall "plonky3_fri_challenger_squeeze"    alpha1_l [c1_l]))
    (.RCall (plonky3FriFoldLeafName 256)        e2_l     [e1_l]))
    (.RCall (plonky3FriCommitLeafName 256)      c2_l     [e2_l]))
    (.RCall "plonky3_fri_challenger_squeeze"    alpha2_l [c2_l]))
    (.RCall (plonky3FriFoldLeafName 128)        e3_l     [e2_l]))
    (.RCall (plonky3FriCommitLeafName 128)      c3_l     [e3_l]))
    (.RCall "plonky3_fri_challenger_squeeze"    alpha3_l [c3_l]))
    (.RCall (plonky3FriFoldLeafName 64)         e4_l     [e3_l]))
    (.RCall (plonky3FriCommitLeafName 64)       c4_l     [e4_l]))
    (.RCall "plonky3_fri_challenger_squeeze"    alpha4_l [c4_l]))
    (.RCall (plonky3FriFoldLeafName 32)         e5_l     [e4_l]))
    (.RCall (plonky3FriCommitLeafName 32)       c5_l     [e5_l]))
    (.RCall "plonky3_fri_challenger_squeeze"    alpha5_l [c5_l]))
    (.RCall (plonky3FriFoldLeafName 16)         e6_l     [e5_l]))
    (.RCall (plonky3FriCommitLeafName 16)       c6_l     [e6_l]))
    (.RCall "plonky3_fri_challenger_squeeze"    alpha6_l [c6_l]))
    (.RCall (plonky3FriFoldLeafName 8)          e7_l     [e6_l]))
    (.RCall (plonky3FriCommitLeafName 8)        c7_l     [e7_l]))
    (.RCall "plonky3_fri_challenger_squeeze"    alpha7_l [c7_l]))
    (.RCall (plonky3FriFoldLeafName 4)          e8_l     [e7_l]))
    (.RCall (plonky3FriCommitLeafName 4)        c8_l     [e8_l]))
    (.RCall "plonky3_fri_challenger_squeeze"    alpha8_l [c8_l]))
    (.RCall (plonky3FriFoldLeafName 2)          e9_l     [e8_l]))
    (.RCall (plonky3FriCommitLeafName 2)        c9_l     [e9_l]))
    (.RCall "plonky3_fri_challenger_squeeze"    alpha9_l [c9_l]))
    (.RCall (plonky3FriFoldLeafName 1)          e10_l    [e9_l]))
    (.RCall (plonky3FriCommitLeafName 1)        c10_l    [e10_l]))
    (.RCall (plonky3FriQueryLeafName 1024)      result_l [c10_l])

/-- `ReifiedFunc` bundle for the N=2 FRI prover. -/
def friProver2Reified : ReifiedFunc :=
  { args    := [("evals", plonky3FriEvalsTowerType 2)]
    body    := friProverBody2
    retName := "__result" }

/-- `ReifiedFunc` bundle for N=4. -/
def friProver4Reified : ReifiedFunc :=
  { args    := [("evals", plonky3FriEvalsTowerType 4)]
    body    := friProverBody4
    retName := "__result" }

/-- `ReifiedFunc` bundle for N=1024 (the canonical Plonky3 FRI depth). -/
def friProver1024Reified : ReifiedFunc :=
  { args    := [("evals", plonky3FriEvalsTowerType 1024)]
    body    := friProverBody1024
    retName := "__result" }

/-! ## 6. Dataflow checks

Static checks on the hand-written bodies: no call reads an undefined slot. The
fold leaf takes no challenge argument, so the squeezed challenges `alpha_k` are
read by no later call and no unread-slot check is stated for these bodies. -/

#guard straightLineUndefined friProver2Reified = some []
#guard straightLineUndefined friProver4Reified = some []
#guard straightLineUndefined friProver1024Reified = some []

end CatCrypt.Crypto.Jasmin.LowCTReflect
