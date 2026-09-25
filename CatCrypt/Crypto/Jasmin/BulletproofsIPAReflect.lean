/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.MsmReflect
public import CatCrypt.Crypto.Jasmin.MsmReflect
public meta import CatCrypt.Crypto.Jasmin.LowCTStraightLineCheck

/-!
# Bulletproofs inner-product-argument prover orchestration over opaque leaves

The Bulletproofs prover's hot path is the inner-product-argument (IPA)
reduction: each round computes two cross commitments `L`, `R` from the current
witness and generator vectors, squeezes a Fiat–Shamir challenge `u`, and folds
both vectors by `u`/`u⁻¹`, halving their length. After `log2 n` rounds the
witness collapses to a scalar and the prover sends it.

This file states that orchestration at `n = 8` (three rounds) as a pure Lean
function `ipaProverLean8` over leaf functions, and supplies a hand-written
`LowCT` body `ipaProverBody8` with the same call sequence, which the front
lowers to jasmin. The two vector types and the seven leaf functions are opaque constants, and
the two default inhabitants are Lean `axiom`s (11 declarations); they have no
Lean semantics, so nothing in this file states
what a commitment, a fold or a challenge computes. No theorem relates
`ipaProverBody8` to `ipaProverLean8`. The `#guard` checks in §6 constrain the
dataflow of the body: every call argument is defined before it is read, and
the only computed values no later call reads are the initial commitment `P`
and the last generator fold `G3`.

## Prover orchestration

```
  ipa_prove(a_vec, G_vec):                         -- a: witness, G: generators
    P = ipa_commit(a_vec, G_vec)                   -- initial commitment
    for round in 0..log2(n):
      L = ipa_cross_L(a_vec, G_vec)                -- L cross commitment
      R = ipa_cross_R(a_vec, G_vec)                -- R cross commitment
      u = squeeze(L, R)                            -- Fiat–Shamir challenge
      (a_vec, G_vec) = ipa_fold(a_vec, G_vec, u)   -- fold by u / u⁻¹
    return ipa_final(a_vec)                        -- final scalar
```

Each step is one leaf call. The leaf names carry the vector width they act on
(`ipa_cross_L_8`, `ipa_cross_L_4`, `ipa_cross_L_2`; `ipa_fold_wit_4`,
`ipa_fold_wit_2`, `ipa_fold_wit_1` for the output width), because the jasmin
argument arrays shrink after every round.

## References

* Bünz, Bootle, Boneh, Poelstra, Wuille, Maxwell — *Bulletproofs: Short Proofs
  for Confidential Transactions and More*, IEEE S&P 2018.
* `CatCrypt/Crypto/Jasmin/MsmReflect.lean` (the point and scalar types reused
  here).
* `CatCrypt/Crypto/Jasmin/LowCTStraightLineCheck.lean` (the dataflow checks).
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque IPA surface types

The witness and generator vectors are opaque types indexed by their length;
an IPA challenge or final scalar is an `MsmEcScalar` (1 byte on the wire) and a
commitment is an `MsmEcPoint` (2 bytes on the wire). -/

opaque IpaWitnessVec.Impl (N : Nat) : NonemptyType.{0}
/-- The IPA witness vector `a` of length `N` (an opaque type). -/
def IpaWitnessVec (N : Nat) : Type := (IpaWitnessVec.Impl N).type
instance (N : Nat) : Nonempty (IpaWitnessVec N) := (IpaWitnessVec.Impl N).property
/-- An inhabitant. -/ noncomputable opaque IpaWitnessVec.default (N : Nat) : IpaWitnessVec N
noncomputable instance (N : Nat) : Inhabited (IpaWitnessVec N) :=
  ⟨IpaWitnessVec.default N⟩

opaque IpaGenVec.Impl (N : Nat) : NonemptyType.{0}
/-- The IPA generator vector `G` of length `N` (an opaque type). -/
def IpaGenVec (N : Nat) : Type := (IpaGenVec.Impl N).type
instance (N : Nat) : Nonempty (IpaGenVec N) := (IpaGenVec.Impl N).property
/-- An inhabitant. -/ noncomputable opaque IpaGenVec.default (N : Nat) : IpaGenVec N
noncomputable instance (N : Nat) : Inhabited (IpaGenVec N) :=
  ⟨IpaGenVec.default N⟩

/-! ## 2. IPA leaves (opaque constants, lowered as jasmin function symbols)

`ipa_commit`, `ipa_cross_L`, `ipa_cross_R` return an `MsmEcPoint`;
`ipa_squeeze` and `ipa_final` return an `MsmEcScalar`. The declarations fix
only the types; the jasmin implementations are supplied at link time. -/

/-- Initial commitment `P` to the witness under the generators. -/
noncomputable opaque ipa_commit (N : Nat) : IpaWitnessVec N → IpaGenVec N → MsmEcPoint
/-- Left cross commitment `L` of a round. -/
noncomputable opaque ipa_cross_L (N : Nat) : IpaWitnessVec N → IpaGenVec N → MsmEcPoint
/-- Right cross commitment `R` of a round. -/
noncomputable opaque ipa_cross_R (N : Nat) : IpaWitnessVec N → IpaGenVec N → MsmEcPoint
/-- Fiat–Shamir challenge `u` squeezed from `(L, R)`. -/
noncomputable opaque ipa_squeeze : MsmEcPoint → MsmEcPoint → MsmEcScalar
/-- Fold of the witness vector by the challenge, halving its length `2N → N`. -/
noncomputable opaque ipa_fold_wit (N : Nat) : IpaWitnessVec (2 * N) → MsmEcScalar → IpaWitnessVec N
/-- Fold of the generator vector by the challenge, halving its length `2N → N`. -/
noncomputable opaque ipa_fold_gen (N : Nat) : IpaGenVec (2 * N) → MsmEcScalar → IpaGenVec N
/-- Final prover scalar read from a witness vector of length `N`. -/
noncomputable opaque ipa_final (N : Nat) : IpaWitnessVec N → MsmEcScalar

/-! ## 3. `@[rust_cmd_pattern]` registrations (n = 8, log2 n = 3 rounds) -/

@[rust_cmd_pattern]
def ipaCommit8Pattern : LowCTPattern where
  name := "ipa_commit_8"; fnHead := ``ipa_commit; arity := 2; towerType := .TBytes 2

@[rust_cmd_pattern]
def ipaCrossL8Pattern : LowCTPattern where
  name := "ipa_cross_L_8"; fnHead := ``ipa_cross_L; arity := 2; towerType := .TBytes 2

@[rust_cmd_pattern]
def ipaCrossR8Pattern : LowCTPattern where
  name := "ipa_cross_R_8"; fnHead := ``ipa_cross_R; arity := 2; towerType := .TBytes 2

@[rust_cmd_pattern]
def ipaSqueezePattern : LowCTPattern where
  name := "ipa_squeeze"; fnHead := ``ipa_squeeze; arity := 2; towerType := .TBytes 1

@[rust_cmd_pattern]
def ipaFoldWit4Pattern : LowCTPattern where
  name := "ipa_fold_wit_4"; fnHead := ``ipa_fold_wit; arity := 2; towerType := .TBytes 4

@[rust_cmd_pattern]
def ipaFoldGen4Pattern : LowCTPattern where
  name := "ipa_fold_gen_4"; fnHead := ``ipa_fold_gen; arity := 2; towerType := .TBytes 8

@[rust_cmd_pattern]
def ipaFinalPattern : LowCTPattern where
  name := "ipa_final"; fnHead := ``ipa_final; arity := 1; towerType := .TBytes 1

/-! ## 4. Pure-Lean Bulletproofs IPA prover

`ipaProverLean8` is the `n = 8` (3-round) IPA reduction: initial commitment,
three (L, R, squeeze, fold-wit, fold-gen) rounds, each reading the vectors the
previous round folded, and the final scalar of the length-1 witness. -/

/-- The `n = 8` Bulletproofs IPA prover over the opaque leaves. Round `k`
    computes its cross commitments and folds from the round-`k-1` fold outputs
    (the inputs `a`, `G` for round 0); the result is `ipa_final` of the round-2
    witness fold. -/
noncomputable def ipaProverLean8
    (a : IpaWitnessVec 8) (G : IpaGenVec 8) : MsmEcScalar :=
  let _P := ipa_commit 8 a G
  -- round 0 : 8 → 4
  let L0 := ipa_cross_L 8 a G
  let R0 := ipa_cross_R 8 a G
  let u0 := ipa_squeeze L0 R0
  let a1 := ipa_fold_wit 4 a u0
  let G1 := ipa_fold_gen 4 G u0
  -- round 1 : 4 → 2
  let L1 := ipa_cross_L 4 a1 G1
  let R1 := ipa_cross_R 4 a1 G1
  let u1 := ipa_squeeze L1 R1
  let a2 := ipa_fold_wit 2 a1 u1
  let G2 := ipa_fold_gen 2 G1 u1
  -- round 2 : 2 → 1
  let L2 := ipa_cross_L 2 a2 G2
  let R2 := ipa_cross_R 2 a2 G2
  let u2 := ipa_squeeze L2 R2
  let a3 := ipa_fold_wit 1 a2 u2
  let _G3 := ipa_fold_gen 1 G2 u2
  ipa_final 1 a3

/-! ## 5. Hand-written `LowCT` body -/

/-- Wire type of a witness vector of length `N` (1 byte per scalar). -/
def ipaWitnessTowerType (N : Nat) : TowerType := .TBytes (1 * N)
/-- Wire type of a generator vector of length `N` (2 bytes per point). -/
def ipaGenTowerType (N : Nat) : TowerType := .TBytes (2 * N)
/-- Wire type of a commitment point. -/
def ipaPointTowerType : TowerType := .TBytes 2
/-- Wire type of a challenge or final scalar. -/
def ipaScalarTowerType : TowerType := .TBytes 1

/-- The located slot named `n` of wire type `t`. -/
def locBulletproofsIPA (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-- Body for the `n = 8` (3-round) IPA reduction, with the call sequence of
    `ipaProverLean8`. Each round's leaf names carry the vector width it acts on,
    and the slots `a1`/`G1`, `a2`/`G2`, `a3`/`G3` have the lengths 4, 2 and 1
    of the round outputs. -/
def ipaProverBody8 : LowCT :=
  let a_l   := locBulletproofsIPA "a"        (ipaWitnessTowerType 8)
  let G_l   := locBulletproofsIPA "G"        (ipaGenTowerType 8)
  let P_l   := locBulletproofsIPA "P"        ipaPointTowerType
  let L0_l  := locBulletproofsIPA "L0"       ipaPointTowerType
  let R0_l  := locBulletproofsIPA "R0"       ipaPointTowerType
  let u0_l  := locBulletproofsIPA "u0"       ipaScalarTowerType
  let a1_l  := locBulletproofsIPA "a1"       (ipaWitnessTowerType 4)
  let G1_l  := locBulletproofsIPA "G1"       (ipaGenTowerType 4)
  let L1_l  := locBulletproofsIPA "L1"       ipaPointTowerType
  let R1_l  := locBulletproofsIPA "R1"       ipaPointTowerType
  let u1_l  := locBulletproofsIPA "u1"       ipaScalarTowerType
  let a2_l  := locBulletproofsIPA "a2"       (ipaWitnessTowerType 2)
  let G2_l  := locBulletproofsIPA "G2"       (ipaGenTowerType 2)
  let L2_l  := locBulletproofsIPA "L2"       ipaPointTowerType
  let R2_l  := locBulletproofsIPA "R2"       ipaPointTowerType
  let u2_l  := locBulletproofsIPA "u2"       ipaScalarTowerType
  let a3_l  := locBulletproofsIPA "a3"       (ipaWitnessTowerType 1)
  let G3_l  := locBulletproofsIPA "G3"       (ipaGenTowerType 1)
  let res_l := locBulletproofsIPA "__result" ipaScalarTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq
  (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "ipa_commit_8"   P_l   [a_l, G_l]))
    (.RCall "ipa_cross_L_8"  L0_l  [a_l, G_l]))
    (.RCall "ipa_cross_R_8"  R0_l  [a_l, G_l]))
    (.RCall "ipa_squeeze"    u0_l  [L0_l, R0_l]))
    (.RCall "ipa_fold_wit_4" a1_l  [a_l, u0_l]))
    (.RCall "ipa_fold_gen_4" G1_l  [G_l, u0_l]))
    (.RCall "ipa_cross_L_4"  L1_l  [a1_l, G1_l]))
    (.RCall "ipa_cross_R_4"  R1_l  [a1_l, G1_l]))
    (.RCall "ipa_squeeze"    u1_l  [L1_l, R1_l]))
    (.RCall "ipa_fold_wit_2" a2_l  [a1_l, u1_l]))
    (.RCall "ipa_fold_gen_2" G2_l  [G1_l, u1_l]))
    (.RCall "ipa_cross_L_2"  L2_l  [a2_l, G2_l]))
    (.RCall "ipa_cross_R_2"  R2_l  [a2_l, G2_l]))
    (.RCall "ipa_squeeze"    u2_l  [L2_l, R2_l]))
    (.RCall "ipa_fold_wit_1" a3_l  [a2_l, u2_l]))
    (.RCall "ipa_fold_gen_1" G3_l  [G2_l, u2_l]))
    (.RCall "ipa_final"      res_l [a3_l])

/-- `ReifiedFunc` bundle for the `n = 8` Bulletproofs IPA prover. -/
def ipaProver8Reified : ReifiedFunc :=
  { args    := [("a", ipaWitnessTowerType 8), ("G", ipaGenTowerType 8)]
    body    := ipaProverBody8
    retName := "__result" }

/-! ## 6. Dataflow checks

Static checks on the hand-written body: no call reads an undefined slot, and
the only computed slots no later call reads are the initial commitment `P` and
the last generator fold `G3`. -/

#guard straightLineUndefined ipaProver8Reified = some []
#guard straightLineUnread ipaProver8Reified = some ["P", "G3"]

end CatCrypt.Crypto.Jasmin.LowCTReflect
