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
# Halo2 IPA prover orchestration over opaque leaves

Halo2's polynomial-commitment layer is the inner-product argument (IPA) over
the Pasta cycle. The prover commits to the witness polynomial, evaluates the
permutation and gate identities for the transcript, then opens via the IPA
reduction: each of `log2 n` rounds forms two cross commitments `L`, `R` from
the current coefficient and generator vectors, squeezes a challenge `u`, and
folds both vectors by `u`/`u⁻¹`, halving their length.

This file states that orchestration at `n = 8` (three rounds) as a pure Lean
function `halo2IPAProverLean8` over leaf functions, and supplies a hand-written
`LowCT` body `halo2IPAProverBody8` with the same call sequence, which the front
lowers to jasmin. The two vector types and the eight leaf functions are opaque constants, and
the two default inhabitants are Lean `axiom`s (12 declarations); they have no
Lean semantics, so nothing in this file states
what a commitment, a gate round, a fold or a challenge computes. No theorem
relates `halo2IPAProverBody8` to `halo2IPAProverLean8`. The `#guard` checks in
§6 constrain the dataflow of the body: every call argument is defined before it
is read, and the only computed values no later call reads are the witness
commitment `cmt`, the gate-round scalar `cg` and the last generator fold `G3`.

## Prover orchestration

```
  halo2_prove(coeffs, gens):                          -- coeffs: poly, gens: points
    cmt   = halo2_commit(coeffs, gens)                -- witness commitment
    cg    = halo2_gate_round(coeffs)                  -- permutation/gate identities
    -- IPA opening (log2 n rounds):
    for round in 0..log2(n):
      L = halo2_ipa_L(coeffs, gens)                   -- L cross commitment
      R = halo2_ipa_R(coeffs, gens)                   -- R cross commitment
      u = halo2_squeeze(L, R)                         -- Fiat–Shamir challenge
      coeffs = halo2_fold_coeffs(coeffs, u)           -- fold by u / u⁻¹
      gens   = halo2_fold_gens(gens, u)               -- fold by u⁻¹ / u
    return halo2_ipa_open(coeffs)                     -- final opening scalar
```

Each step is one leaf call. The leaf names carry the vector width they act on
(`halo2_ipa_L_8`, `halo2_ipa_L_4`, `halo2_ipa_L_2`; `halo2_fold_coeffs_4`,
`halo2_fold_coeffs_2`, `halo2_fold_coeffs_1` for the output width), because the
jasmin argument arrays shrink after every round.

## References

* Bowe, Grigg, Hopwood — *Recursive Proof Composition without a Trusted Setup*,
  2019 (Halo / Halo2 / Pasta-cycle IPA).
* Sibling: `CatCrypt/Crypto/Jasmin/BulletproofsIPAReflect.lean`.
* `CatCrypt/Crypto/Jasmin/LowCTStraightLineCheck.lean` (the dataflow checks).
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque Halo2 IPA surface types

The coefficient and generator vectors are opaque types indexed by their
length; an IPA challenge or opening scalar is an `MsmEcScalar` (1 byte on the
wire) and a commitment is an `MsmEcPoint` (2 bytes on the wire). -/

opaque Halo2CoeffVec.Impl (N : Nat) : NonemptyType.{0}
/-- The Halo2 coefficient vector of length `N` (an opaque type). -/
def Halo2CoeffVec (N : Nat) : Type := (Halo2CoeffVec.Impl N).type
instance (N : Nat) : Nonempty (Halo2CoeffVec N) := (Halo2CoeffVec.Impl N).property
/-- An inhabitant. -/ noncomputable opaque Halo2CoeffVec.default (N : Nat) : Halo2CoeffVec N
noncomputable instance (N : Nat) : Inhabited (Halo2CoeffVec N) :=
  ⟨Halo2CoeffVec.default N⟩

opaque Halo2GenVec.Impl (N : Nat) : NonemptyType.{0}
/-- The Halo2 generator vector `G` of length `N` (an opaque type). -/
def Halo2GenVec (N : Nat) : Type := (Halo2GenVec.Impl N).type
instance (N : Nat) : Nonempty (Halo2GenVec N) := (Halo2GenVec.Impl N).property
/-- An inhabitant. -/ noncomputable opaque Halo2GenVec.default (N : Nat) : Halo2GenVec N
noncomputable instance (N : Nat) : Inhabited (Halo2GenVec N) :=
  ⟨Halo2GenVec.default N⟩

/-! ## 2. Halo2 IPA leaves (opaque constants, lowered as jasmin function symbols)

`halo2_commit`, `halo2_ipa_L`, `halo2_ipa_R` return an `MsmEcPoint`;
`halo2_gate_round`, `halo2_squeeze` and `halo2_ipa_open` return an
`MsmEcScalar`. The declarations fix only the types; the jasmin implementations
are supplied at link time. -/

/-- Witness commitment `cmt` to the coefficients under the generators. -/
noncomputable opaque halo2_commit (N : Nat) : Halo2CoeffVec N → Halo2GenVec N → MsmEcPoint
/-- Batched permutation/gate-identity evaluation for the transcript round. -/
noncomputable opaque halo2_gate_round (N : Nat) : Halo2CoeffVec N → MsmEcScalar
/-- Left cross commitment `L` of an IPA round. -/
noncomputable opaque halo2_ipa_L (N : Nat) : Halo2CoeffVec N → Halo2GenVec N → MsmEcPoint
/-- Right cross commitment `R` of an IPA round. -/
noncomputable opaque halo2_ipa_R (N : Nat) : Halo2CoeffVec N → Halo2GenVec N → MsmEcPoint
/-- Fiat–Shamir challenge `u` squeezed from `(L, R)`. -/
noncomputable opaque halo2_squeeze : MsmEcPoint → MsmEcPoint → MsmEcScalar
/-- Fold of the coefficient vector by the challenge, halving its length `2N → N`. -/
noncomputable opaque halo2_fold_coeffs (N : Nat) : Halo2CoeffVec (2 * N) → MsmEcScalar → Halo2CoeffVec N
/-- Fold of the generator vector by the challenge, halving its length `2N → N`. -/
noncomputable opaque halo2_fold_gens (N : Nat) : Halo2GenVec (2 * N) → MsmEcScalar → Halo2GenVec N
/-- Final IPA opening scalar read from a coefficient vector of length `N`. -/
noncomputable opaque halo2_ipa_open (N : Nat) : Halo2CoeffVec N → MsmEcScalar

/-! ## 3. `@[rust_cmd_pattern]` registrations (n = 8, log2 n = 3 rounds) -/

@[rust_cmd_pattern]
def halo2Commit8Pattern : LowCTPattern where
  name := "halo2_commit_8"; fnHead := ``halo2_commit; arity := 2; towerType := .TBytes 2

@[rust_cmd_pattern]
def halo2GateRound8Pattern : LowCTPattern where
  name := "halo2_gate_round_8"; fnHead := ``halo2_gate_round; arity := 1; towerType := .TBytes 1

@[rust_cmd_pattern]
def halo2IpaL8Pattern : LowCTPattern where
  name := "halo2_ipa_L_8"; fnHead := ``halo2_ipa_L; arity := 2; towerType := .TBytes 2

@[rust_cmd_pattern]
def halo2IpaR8Pattern : LowCTPattern where
  name := "halo2_ipa_R_8"; fnHead := ``halo2_ipa_R; arity := 2; towerType := .TBytes 2

@[rust_cmd_pattern]
def halo2SqueezePattern : LowCTPattern where
  name := "halo2_squeeze"; fnHead := ``halo2_squeeze; arity := 2; towerType := .TBytes 1

@[rust_cmd_pattern]
def halo2FoldCoeffs4Pattern : LowCTPattern where
  name := "halo2_fold_coeffs_4"; fnHead := ``halo2_fold_coeffs; arity := 2; towerType := .TBytes 4

@[rust_cmd_pattern]
def halo2FoldGens4Pattern : LowCTPattern where
  name := "halo2_fold_gens_4"; fnHead := ``halo2_fold_gens; arity := 2; towerType := .TBytes 8

@[rust_cmd_pattern]
def halo2IpaOpenPattern : LowCTPattern where
  name := "halo2_ipa_open"; fnHead := ``halo2_ipa_open; arity := 1; towerType := .TBytes 1

/-! ## 4. Pure-Lean Halo2 IPA prover

`halo2IPAProverLean8` is the `n = 8` (3-round) Halo2 IPA opening: witness
commitment, gate/permutation transcript round, three (L, R, squeeze,
fold-coeffs, fold-gens) rounds, each reading the vectors the previous round
folded, and the opening of the length-1 coefficient vector. -/

/-- The `n = 8` Halo2 IPA prover over the opaque leaves. Round `k`
    computes its cross commitments and folds from the round-`k-1` fold outputs
    (the inputs `coeffs`, `G` for round 0); the result is `halo2_ipa_open` of
    the round-2 coefficient fold. -/
noncomputable def halo2IPAProverLean8
    (coeffs : Halo2CoeffVec 8) (G : Halo2GenVec 8) : MsmEcScalar :=
  let _cmt := halo2_commit 8 coeffs G
  let _cg  := halo2_gate_round 8 coeffs
  -- round 0 : 8 → 4
  let L0 := halo2_ipa_L 8 coeffs G
  let R0 := halo2_ipa_R 8 coeffs G
  let u0 := halo2_squeeze L0 R0
  let c1 := halo2_fold_coeffs 4 coeffs u0
  let G1 := halo2_fold_gens 4 G u0
  -- round 1 : 4 → 2
  let L1 := halo2_ipa_L 4 c1 G1
  let R1 := halo2_ipa_R 4 c1 G1
  let u1 := halo2_squeeze L1 R1
  let c2 := halo2_fold_coeffs 2 c1 u1
  let G2 := halo2_fold_gens 2 G1 u1
  -- round 2 : 2 → 1
  let L2 := halo2_ipa_L 2 c2 G2
  let R2 := halo2_ipa_R 2 c2 G2
  let u2 := halo2_squeeze L2 R2
  let c3 := halo2_fold_coeffs 1 c2 u2
  let _G3 := halo2_fold_gens 1 G2 u2
  halo2_ipa_open 1 c3

/-! ## 5. Hand-written `LowCT` body -/

/-- Wire type of a coefficient vector of length `N` (1 byte per scalar). -/
def halo2CoeffTowerType (N : Nat) : TowerType := .TBytes (1 * N)
/-- Wire type of a generator vector of length `N` (2 bytes per point). -/
def halo2GenTowerType (N : Nat) : TowerType := .TBytes (2 * N)
/-- Wire type of a commitment point. -/
def halo2PointTowerType : TowerType := .TBytes 2
/-- Wire type of a challenge, gate-round or opening scalar. -/
def halo2ScalarTowerType : TowerType := .TBytes 1

/-- The located slot named `n` of wire type `t`. -/
def locHalo2IPAProver (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-- Body for the `n = 8` (3-round) Halo2 IPA opening, with the call sequence of
    `halo2IPAProverLean8`. Each round's leaf names carry the vector width it
    acts on, and the slots `c1`/`G1`, `c2`/`G2`, `c3`/`G3` have the lengths 4, 2
    and 1 of the round outputs. -/
def halo2IPAProverBody8 : LowCT :=
  let c_l   := locHalo2IPAProver "coeffs"   (halo2CoeffTowerType 8)
  let G_l   := locHalo2IPAProver "G"        (halo2GenTowerType 8)
  let cmt_l := locHalo2IPAProver "cmt"      halo2PointTowerType
  let cg_l  := locHalo2IPAProver "cg"       halo2ScalarTowerType
  let L0_l  := locHalo2IPAProver "L0"       halo2PointTowerType
  let R0_l  := locHalo2IPAProver "R0"       halo2PointTowerType
  let u0_l  := locHalo2IPAProver "u0"       halo2ScalarTowerType
  let c1_l  := locHalo2IPAProver "c1"       (halo2CoeffTowerType 4)
  let G1_l  := locHalo2IPAProver "G1"       (halo2GenTowerType 4)
  let L1_l  := locHalo2IPAProver "L1"       halo2PointTowerType
  let R1_l  := locHalo2IPAProver "R1"       halo2PointTowerType
  let u1_l  := locHalo2IPAProver "u1"       halo2ScalarTowerType
  let c2_l  := locHalo2IPAProver "c2"       (halo2CoeffTowerType 2)
  let G2_l  := locHalo2IPAProver "G2"       (halo2GenTowerType 2)
  let L2_l  := locHalo2IPAProver "L2"       halo2PointTowerType
  let R2_l  := locHalo2IPAProver "R2"       halo2PointTowerType
  let u2_l  := locHalo2IPAProver "u2"       halo2ScalarTowerType
  let c3_l  := locHalo2IPAProver "c3"       (halo2CoeffTowerType 1)
  let G3_l  := locHalo2IPAProver "G3"       (halo2GenTowerType 1)
  let res_l := locHalo2IPAProver "__result" halo2ScalarTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq
  (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "halo2_commit_8"      cmt_l [c_l, G_l]))
    (.RCall "halo2_gate_round_8"  cg_l  [c_l]))
    (.RCall "halo2_ipa_L_8"       L0_l  [c_l, G_l]))
    (.RCall "halo2_ipa_R_8"       R0_l  [c_l, G_l]))
    (.RCall "halo2_squeeze"       u0_l  [L0_l, R0_l]))
    (.RCall "halo2_fold_coeffs_4" c1_l  [c_l, u0_l]))
    (.RCall "halo2_fold_gens_4"   G1_l  [G_l, u0_l]))
    (.RCall "halo2_ipa_L_4"       L1_l  [c1_l, G1_l]))
    (.RCall "halo2_ipa_R_4"       R1_l  [c1_l, G1_l]))
    (.RCall "halo2_squeeze"       u1_l  [L1_l, R1_l]))
    (.RCall "halo2_fold_coeffs_2" c2_l  [c1_l, u1_l]))
    (.RCall "halo2_fold_gens_2"   G2_l  [G1_l, u1_l]))
    (.RCall "halo2_ipa_L_2"       L2_l  [c2_l, G2_l]))
    (.RCall "halo2_ipa_R_2"       R2_l  [c2_l, G2_l]))
    (.RCall "halo2_squeeze"       u2_l  [L2_l, R2_l]))
    (.RCall "halo2_fold_coeffs_1" c3_l  [c2_l, u2_l]))
    (.RCall "halo2_fold_gens_1"   G3_l  [G2_l, u2_l]))
    (.RCall "halo2_ipa_open"      res_l [c3_l])

/-- `ReifiedFunc` bundle for the `n = 8` Halo2 IPA prover. -/
def halo2IPAProver8Reified : ReifiedFunc :=
  { args    := [("coeffs", halo2CoeffTowerType 8), ("G", halo2GenTowerType 8)]
    body    := halo2IPAProverBody8
    retName := "__result" }

/-! ## 6. Dataflow checks

Static checks on the hand-written body: no call reads an undefined slot, and
the only computed slots no later call reads are `cmt`, `cg` and the last
generator fold `G3`. -/

#guard straightLineUndefined halo2IPAProver8Reified = some []
#guard straightLineUnread halo2IPAProver8Reified = some ["cmt", "cg", "G3"]

end CatCrypt.Crypto.Jasmin.LowCTReflect
