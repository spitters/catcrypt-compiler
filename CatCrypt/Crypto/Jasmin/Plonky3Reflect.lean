/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# Plonky3 Merkle reflect surface — Tier A migration of the Merkle layer

Layer 1 of the Plonky3 STARK chain (binary Merkle tree commitment over
BabyBear leaves) lifted through the verified compiler chain
`LowCT → CryptoSSA → Com → jasmin`.

This is the **architectural opposite** of the legacy
`CatCrypt/Crypto/SecureCompilation/VIR/Plonky3MerkleEmit.lean` string-template
emit (`bench/plonky3_compare/gen/merkle_build_root.jazz` is built by
`String.intercalate` — out-of-chain by construction). This file is the
lattice-Merkle analogue of `FalconReflect.lean` (#191): every byte of the
new emit goes through the verified front.

## Merkle equation

```
  merkle_build_root(leaves : [Field; N]):
    digests_0  = [hash_leaf(leaves[i]) for i in 0..N]              -- per-leaf hash
    digests_k  = [compress(digests_{k-1}[2j], digests_{k-1}[2j+1]) -- level k
                  for j in 0..N/2^k]                               for k in 1..log2 N
    return digests_{log2 N}[0]                                     -- the root
```

We model each major step as one opaque leaf call:

| Lean axiom                       | Leaf name (.jazz)              | TowerType         |
|----------------------------------|--------------------------------|-------------------|
| `plonky3_merkle_hash_leaves_N`   | `plonky3_merkle_hash_leaves_N` | `TBytes (32·N)`   |
| `plonky3_merkle_level_M`         | `plonky3_merkle_level_M`       | `TBytes (32·M)`   |
| `plonky3_merkle_extract_root`    | `plonky3_merkle_extract_root`  | `TBytes 32`       |

A full `build_root` over `N = 2^k` leaves is one RCall to `hash_leaves` followed
by `k` RCalls to `level_M` for `M ∈ {N/2, N/4, ..., 1}`, then `extract_root`
producing the 32-byte digest. The level loop is **statically unrolled** into a
flat `RSeq` chain — `RFor` is not consumed by `translate` (see
`LowCTToCryptoSSA.lean:752`), so flat unrolling is the only path through the
verified front. For each target depth `k`, we emit one `ReifiedFunc`.

## Reflection→front gap

Same as `FalconReflect.lean` and `MemAbiReflect.lean`: `reifyLowCT%` does not
consult the `LowCTPattern` registry, so we hand-build the `LowCT` body the
reifier *would* produce. The rest of the front (`translate → cryptoDialectToJasminCom →
emitAbiOrchRegPtr`) is unchanged.

## Relation to legacy Tier C `Plonky3MerkleEmit.lean`

The legacy file emits its `.jazz` via `String.intercalate` (no compiler
correctness theorem witnesses the body). This file replaces that pattern with
an in-chain emit: same final artifact shape, routed through the verified
compiler. The legacy emit is kept as an out-of-chain reference until the
`bench/plonky3_compare` C harness migrates.

## References

* Plonky3 Merkle commitment: `plonky3-hax/src/specs/merkle.rs`
* Mirror pattern: `CatCrypt/Crypto/Jasmin/FalconReflect.lean` (#191)
* Driver template: `bench/fndsa_compare/verify_from_rustcmd.lean`
-/

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque Plonky3 Merkle surface types

The reflect surface treats one Merkle level as an opaque byte buffer of
`32 · m` bytes (`m` digests of 32 bytes each). The two-to-one compress and
per-leaf hash are taken as leaf calls; the verified pipeline emits the
orchestration. -/

/-- A 32-byte Plonky3 Merkle digest (matches `Digest = [u8; 32]` in
    `plonky3-hax/src/specs/merkle.rs`). Opaque on the Lean side; the leaf
    `plonky3_poseidon2_compress` implements the byte-mixing under the hood. -/
axiom Plonky3Digest : Type
/-- Axiomatic inhabitant. -/ axiom Plonky3Digest.default : Plonky3Digest
noncomputable instance : Inhabited Plonky3Digest := ⟨Plonky3Digest.default⟩

/-- A buffer of `N` packed leaf values (8 bytes per BabyBear field element).
    The `plonky3_merkle_hash_leaves_N` leaf consumes `N · 8` bytes and produces
    `N` digests = `N · 32` bytes. Opaque; the actual byte-layout is the leaf's
    business. -/
axiom Plonky3Leaves (N : Nat) : Type
/-- Axiomatic inhabitant. -/ axiom Plonky3Leaves.default (N : Nat) : Plonky3Leaves N
noncomputable instance (N : Nat) : Inhabited (Plonky3Leaves N) :=
  ⟨Plonky3Leaves.default N⟩

/-- A buffer of `M` packed digests (`32 · M` bytes). Used to type the per-level
    arrays; one `plonky3_merkle_level_M` call consumes a `Plonky3DigestArr (2·M)`
    and produces a `Plonky3DigestArr M`. -/
axiom Plonky3DigestArr (M : Nat) : Type
/-- Axiomatic inhabitant. -/ axiom Plonky3DigestArr.default (M : Nat) : Plonky3DigestArr M
noncomputable instance (M : Nat) : Inhabited (Plonky3DigestArr M) :=
  ⟨Plonky3DigestArr.default M⟩

/-! ## 2. Merkle leaves (axioms = opaque jasmin function symbols)

Each leaf is parameterised by its array-width (the surface size in digests);
a single emit instantiates these at a fixed depth `k`, so the leaves below
are family-indexed by Nat. -/

/-- Bulk leaf hash: `digests = [hash_leaf(leaves[i]) for i in 0..N]`. -/
axiom plonky3_merkle_hash_leaves (N : Nat) :
    Plonky3Leaves N → Plonky3DigestArr N

/-- One Merkle level: `parents[j] = compress(children[2j], children[2j+1])` for
    `j ∈ [0, M)`. The input has `2·M` digests, the output has `M`. Implementation
    is Poseidon2 two-to-one compress per pair (the reference `merkle.rs`
    `hash_two_to_one`). -/
axiom plonky3_merkle_level (M : Nat) :
    Plonky3DigestArr (2 * M) → Plonky3DigestArr M

/-- Extract the singleton root from a width-1 digest array. -/
axiom plonky3_merkle_extract_root :
    Plonky3DigestArr 1 → Plonky3Digest

/-! ## 3. `@[rust_cmd_pattern]` registrations (per fixed N) -/

/-- Register `plonky3_merkle_hash_leaves` (N=1024 specialisation). -/
@[rust_cmd_pattern]
def plonky3MerkleHashLeaves1024Pattern : LowCTPattern where
  name      := "plonky3_merkle_hash_leaves_1024"
  fnHead    := ``plonky3_merkle_hash_leaves
  arity     := 1
  towerType := .TBytes (32 * 1024)

/-- Register `plonky3_merkle_level` (M=512: first level of N=1024). -/
@[rust_cmd_pattern]
def plonky3MerkleLevel512Pattern : LowCTPattern where
  name      := "plonky3_merkle_level_512"
  fnHead    := ``plonky3_merkle_level
  arity     := 1
  towerType := .TBytes (32 * 512)

/-- Register `plonky3_merkle_extract_root`. -/
@[rust_cmd_pattern]
def plonky3MerkleExtractRootPattern : LowCTPattern where
  name      := "plonky3_merkle_extract_root"
  fnHead    := ``plonky3_merkle_extract_root
  arity     := 1
  towerType := .TBytes 32

/-! ## 4. Pure-Lean Merkle build-root function

Each `merkleBuildRootLean_<N>` is the pure Lean specification for the
fixed-depth emit. The body is a flat let-chain mirroring the
hand-built `LowCT` exactly. -/

/-- Pure-Lean build-root for `N = 4` leaves (`log2 N = 2`: two level calls). -/
noncomputable def merkleBuildRootLean4 (leaves : Plonky3Leaves 4) : Plonky3Digest :=
  let d0   := plonky3_merkle_hash_leaves 4 leaves      -- 4 digests
  let d1   := plonky3_merkle_level 2 d0                -- 2 digests
  let d2   := plonky3_merkle_level 1 d1                -- 1 digest (the root array)
  plonky3_merkle_extract_root d2

/-- Pure-Lean build-root for `N = 2` leaves (`log2 N = 1`: one level call). -/
noncomputable def merkleBuildRootLean2 (leaves : Plonky3Leaves 2) : Plonky3Digest :=
  let d0   := plonky3_merkle_hash_leaves 2 leaves      -- 2 digests
  let d1   := plonky3_merkle_level 1 d0                -- 1 digest
  plonky3_merkle_extract_root d1

/-- Pure-Lean build-root for `N = 1024` leaves (`log2 N = 10`: ten level calls). -/
noncomputable def merkleBuildRootLean1024 (leaves : Plonky3Leaves 1024) :
    Plonky3Digest :=
  let d0   := plonky3_merkle_hash_leaves 1024 leaves
  let d1   := plonky3_merkle_level 512 d0
  let d2   := plonky3_merkle_level 256 d1
  let d3   := plonky3_merkle_level 128 d2
  let d4   := plonky3_merkle_level 64  d3
  let d5   := plonky3_merkle_level 32  d4
  let d6   := plonky3_merkle_level 16  d5
  let d7   := plonky3_merkle_level 8   d6
  let d8   := plonky3_merkle_level 4   d7
  let d9   := plonky3_merkle_level 2   d8
  let d10  := plonky3_merkle_level 1   d9
  plonky3_merkle_extract_root d10

/-! ## 5. Hand-built `LowCT` bodies — the front-end input

Each level becomes one `RCall` of leaf `plonky3_merkle_level_<M>` with a fresh
destination of `TBytes (32 · M)`. The first `RCall` is `plonky3_merkle_hash_leaves_N`
(leaves-buffer → first-level digest-array), the last is
`plonky3_merkle_extract_root` (digest-arr-1 → root digest).

`reifyLowCT%` does not consult the registry, so we hand-build the body.
Downstream (`translate → cryptoDialectToJasminCom → emitAbiOrchRegPtr`) is unmodified. -/

/-- TowerType for the BabyBear leaves buffer of size `N` (8 bytes/elem). -/
def plonky3LeavesTowerType (N : Nat) : TowerType := .TBytes (8 * N)
/-- TowerType for the per-level digest array of width `M` (32 bytes/digest). -/
def plonky3DigestArrTowerType (M : Nat) : TowerType := .TBytes (32 * M)
/-- TowerType for the final 32-byte root digest. -/
def plonky3RootTowerType : TowerType := .TBytes 32

private def loc (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-- Per-level leaf names use the array width as suffix: e.g. `plonky3_merkle_level_2`. -/
def plonky3LevelLeafName (M : Nat) : String :=
  "plonky3_merkle_level_" ++ toString M

/-- Per-N leaves hash leaf name. -/
def plonky3HashLeavesLeafName (N : Nat) : String :=
  "plonky3_merkle_hash_leaves_" ++ toString N

/-- Body for `N = 2`: one hash-leaves, one level call, one extract. -/
def merkleBuildRootBody2 : LowCT :=
  let leaves_l := loc "leaves" (plonky3LeavesTowerType 2)
  let d0_l     := loc "d0"     (plonky3DigestArrTowerType 2)
  let d1_l     := loc "d1"     (plonky3DigestArrTowerType 1)
  let result_l := loc "__result" plonky3RootTowerType
  .RSeq (.RSeq (.RSeq .RSkip
    (.RCall (plonky3HashLeavesLeafName 2) d0_l [leaves_l]))
    (.RCall (plonky3LevelLeafName 1)     d1_l [d0_l]))
    (.RCall "plonky3_merkle_extract_root" result_l [d1_l])

/-- Body for `N = 4`: one hash-leaves, 2 level calls, one extract. -/
def merkleBuildRootBody4 : LowCT :=
  let leaves_l := loc "leaves" (plonky3LeavesTowerType 4)
  let d0_l     := loc "d0"     (plonky3DigestArrTowerType 4)
  let d1_l     := loc "d1"     (plonky3DigestArrTowerType 2)
  let d2_l     := loc "d2"     (plonky3DigestArrTowerType 1)
  let result_l := loc "__result" plonky3RootTowerType
  .RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall (plonky3HashLeavesLeafName 4) d0_l [leaves_l]))
    (.RCall (plonky3LevelLeafName 2)     d1_l [d0_l]))
    (.RCall (plonky3LevelLeafName 1)     d2_l [d1_l]))
    (.RCall "plonky3_merkle_extract_root" result_l [d2_l])

/-- Body for `N = 1024`: one hash-leaves, 10 level calls, one extract. -/
def merkleBuildRootBody1024 : LowCT :=
  let leaves_l := loc "leaves" (plonky3LeavesTowerType 1024)
  let d0_l     := loc "d0"     (plonky3DigestArrTowerType 1024)
  let d1_l     := loc "d1"     (plonky3DigestArrTowerType 512)
  let d2_l     := loc "d2"     (plonky3DigestArrTowerType 256)
  let d3_l     := loc "d3"     (plonky3DigestArrTowerType 128)
  let d4_l     := loc "d4"     (plonky3DigestArrTowerType 64)
  let d5_l     := loc "d5"     (plonky3DigestArrTowerType 32)
  let d6_l     := loc "d6"     (plonky3DigestArrTowerType 16)
  let d7_l     := loc "d7"     (plonky3DigestArrTowerType 8)
  let d8_l     := loc "d8"     (plonky3DigestArrTowerType 4)
  let d9_l     := loc "d9"     (plonky3DigestArrTowerType 2)
  let d10_l    := loc "d10"    (plonky3DigestArrTowerType 1)
  let result_l := loc "__result" plonky3RootTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq
    .RSkip
    (.RCall (plonky3HashLeavesLeafName 1024) d0_l  [leaves_l]))
    (.RCall (plonky3LevelLeafName 512)        d1_l  [d0_l]))
    (.RCall (plonky3LevelLeafName 256)        d2_l  [d1_l]))
    (.RCall (plonky3LevelLeafName 128)        d3_l  [d2_l]))
    (.RCall (plonky3LevelLeafName 64)         d4_l  [d3_l]))
    (.RCall (plonky3LevelLeafName 32)         d5_l  [d4_l]))
    (.RCall (plonky3LevelLeafName 16)         d6_l  [d5_l]))
    (.RCall (plonky3LevelLeafName 8)          d7_l  [d6_l]))
    (.RCall (plonky3LevelLeafName 4)          d8_l  [d7_l]))
    (.RCall (plonky3LevelLeafName 2)          d9_l  [d8_l]))
    (.RCall (plonky3LevelLeafName 1)          d10_l [d9_l]))
    (.RCall "plonky3_merkle_extract_root" result_l [d10_l])

/-- `ReifiedFunc` bundle for the N=2 build-root (mirrors what `reifyLowCT%`
    would produce for `merkleBuildRootLean2`). -/
def merkleBuildRoot2Reified : ReifiedFunc :=
  { args    := [("leaves", plonky3LeavesTowerType 2)]
    body    := merkleBuildRootBody2
    retName := "__result" }

/-- `ReifiedFunc` bundle for N=4. -/
def merkleBuildRoot4Reified : ReifiedFunc :=
  { args    := [("leaves", plonky3LeavesTowerType 4)]
    body    := merkleBuildRootBody4
    retName := "__result" }

/-- `ReifiedFunc` bundle for N=1024. -/
def merkleBuildRoot1024Reified : ReifiedFunc :=
  { args    := [("leaves", plonky3LeavesTowerType 1024)]
    body    := merkleBuildRootBody1024
    retName := "__result" }

/-! ## 6. Single-leaf body — KAT-friendly variant

For the small-N KAT (N=1: the degenerate "tree" with one leaf = the hash itself),
we emit a one-call body: `plonky3_merkle_hash_leaves_1 → plonky3_merkle_extract_root`.
This is the simplest Tier A driver in the file — a sanity check that the chain
fires on the trivial input. -/

/-- Pure-Lean build-root for `N = 1` (one leaf, no level calls). -/
noncomputable def merkleBuildRootLean1 (leaves : Plonky3Leaves 1) : Plonky3Digest :=
  let d0 := plonky3_merkle_hash_leaves 1 leaves
  plonky3_merkle_extract_root d0

/-- Body for `N = 1`. -/
def merkleBuildRootBody1 : LowCT :=
  let leaves_l := loc "leaves" (plonky3LeavesTowerType 1)
  let d0_l     := loc "d0"     (plonky3DigestArrTowerType 1)
  let result_l := loc "__result" plonky3RootTowerType
  .RSeq (.RSeq .RSkip
    (.RCall (plonky3HashLeavesLeafName 1) d0_l [leaves_l]))
    (.RCall "plonky3_merkle_extract_root" result_l [d0_l])

/-- `ReifiedFunc` bundle for N=1 (trivial tree). -/
def merkleBuildRoot1Reified : ReifiedFunc :=
  { args    := [("leaves", plonky3LeavesTowerType 1)]
    body    := merkleBuildRootBody1
    retName := "__result" }

/-! ## 7. Inspection -/

#eval merkleBuildRoot2Reified.args.map Prod.fst              -- [leaves]
#eval merkleBuildRoot4Reified.args.length                    -- 1
#eval merkleBuildRoot1024Reified.retName                     -- __result
#eval merkleBuildRoot1Reified.args.length                    -- 1

open Lean in
#eval show Lean.MetaM _ from do
  LowCTPattern.taggedDecls
  -- expect Plonky3 patterns: hash_leaves_1024, level_512, extract_root (+ Falcon, etc.)

end CatCrypt.Crypto.Jasmin.LowCTReflect
