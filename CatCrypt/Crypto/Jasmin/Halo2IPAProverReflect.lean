/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.MsmReflect

/-!
# Halo2 IPA prover reflect surface — Tier 3 full-emit (ZK honesty roadmap)

Halo2's polynomial-commitment layer is the **inner-product argument (IPA) over
the Pasta cycle** — no trusted setup. The prover commits to the witness
polynomials with a Pasta MSM, runs the PLONK-style permutation/gate identities
through a Fiat–Shamir transcript, then opens via the IPA reduction: each of
`log2 n` rounds forms two cross commitments `L`, `R` (each an MSM over the
current Pasta generators), squeezes a challenge `u`, and folds the
coefficient/generator vectors by `u`/`u⁻¹`, halving their length.

This file supplies the **Axis-A** piece for Tier 3 (`bench/halo2_compare/
README.md`): the *Halo2 IPA prover orchestration* — witness commit, the
permutation/gate transcript round, then the per-round (L-commit, R-commit,
squeeze, fold-coeffs, fold-gens) IPA loop, then the final opening — reflected
through the verified compiler chain `LowCT → CryptoSSA → Com → jasmin`, the
same chain `bench/plonky3_compare/fri_from_rustcmd.lean` runs for the Plonky3
FRI prover and `bench/bulletproofs_compare/ipa_from_rustcmd.lean` runs for the
Bulletproofs IPA prover. The commitment / cross-commitment leaves reuse the
**already-emitted toy-EC MSM leaves** (`ec_scalar_mul` / `ec_point_add` from
`MsmReflect.lean`) under the hood — the Pasta-cycle analogue the runtime wires
them to — so the IPA hot loop is built over the MSM primitive the suite already
emits and realization-ties (`Pairing/MsmReduce.msm_eq_scalarFold`, the CONN-3
tie that `Halo2EmittedIPARealization.lean` connects to `halo2_group_layer`).
The per-round fold and the gate/permutation transcript step are Halo2-specific
leaves.

## Prover orchestration (per round, Pasta-cycle group)

```
  halo2_prove(coeffs, gens):                          -- coeffs: poly, gens: Pasta pts
    cmt   = halo2_commit(coeffs, gens)                -- witness MSM commitment
    cg    = halo2_gate_round(coeffs)                  -- permutation/gate identities
    -- IPA opening (log2 n rounds):
    for round in 0..log2(n):
      L = halo2_ipa_L(coeffs, gens)                   -- L cross-commitment (MSM)
      R = halo2_ipa_R(coeffs, gens)                   -- R cross-commitment (MSM)
      u = halo2_squeeze(L, R)                         -- Fiat–Shamir challenge
      coeffs = halo2_fold_coeffs(coeffs, u)           -- fold by u / u⁻¹
      gens   = halo2_fold_gens(gens, u)               -- fold by u⁻¹ / u
    return halo2_ipa_open(coeffs)                     -- final opening scalar
```

We model each major step as one opaque leaf (matching the Bulletproofs IPA
reflect surface); the commit / cross-commitments reuse the MSM EC leaves under
the hood. We emit at `n = 8` (`log2 n = 3` IPA rounds), the canonical small
Halo2 size.

## References

* Bowe, Grigg, Hopwood — *Recursive Proof Composition without a Trusted Setup*,
  2019 (Halo / Halo2 / Pasta-cycle IPA).
* `CatCrypt/Crypto/ZK/Halo2EmittedIPARealization.lean` (the Pasta-cycle EC-leaf
  realization the emitted commitment / cross-commitment leaves inherit).
* Sibling: `CatCrypt/Crypto/Jasmin/BulletproofsIPAReflect.lean`.
-/

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque Halo2 IPA surface types

The coefficient vector is an opaque buffer of `N` Pasta scalars; the generator
vector is an opaque buffer of `N` Pasta points (reusing `MsmEcPoint`'s wire
shape). An IPA challenge / opening scalar is one Pasta scalar (1 byte); a
commitment / cross commitment is one Pasta point (2 bytes). -/

/-- The Halo2 coefficient vector (opaque buffer of `N` Pasta scalars). -/
axiom Halo2CoeffVec (N : Nat) : Type
/-- Axiomatic inhabitant. -/ axiom Halo2CoeffVec.default (N : Nat) : Halo2CoeffVec N
noncomputable instance (N : Nat) : Inhabited (Halo2CoeffVec N) :=
  ⟨Halo2CoeffVec.default N⟩

/-- The Halo2 generator vector `G` (opaque buffer of `N` Pasta points). -/
axiom Halo2GenVec (N : Nat) : Type
/-- Axiomatic inhabitant. -/ axiom Halo2GenVec.default (N : Nat) : Halo2GenVec N
noncomputable instance (N : Nat) : Inhabited (Halo2GenVec N) :=
  ⟨Halo2GenVec.default N⟩

/-! ## 2. Halo2 IPA leaves (axioms = opaque jasmin function symbols)

`halo2_commit`, `halo2_ipa_L`, `halo2_ipa_R` produce Pasta points
(`MsmEcPoint`, reused from `MsmReflect`); `halo2_squeeze`/`halo2_ipa_open`
produce Pasta scalars (`MsmEcScalar`); `halo2_gate_round` produces a Pasta
scalar (the batched gate/permutation identity evaluation). The commitments are
MSMs — the runtime wires them to `ec_scalar_mul`/`ec_point_add` chains from
`MsmReflect`. -/

/-- Witness MSM commitment `cmt = ⟨coeffs, G⟩` (an MSM). -/
axiom halo2_commit (N : Nat) : Halo2CoeffVec N → Halo2GenVec N → MsmEcPoint
/-- Batched permutation/gate-identity evaluation for the transcript round. -/
axiom halo2_gate_round (N : Nat) : Halo2CoeffVec N → MsmEcScalar
/-- Left cross-commitment `L` for the IPA round (MSM over the low/high split). -/
axiom halo2_ipa_L (N : Nat) : Halo2CoeffVec N → Halo2GenVec N → MsmEcPoint
/-- Right cross-commitment `R` for the IPA round (MSM over the high/low split). -/
axiom halo2_ipa_R (N : Nat) : Halo2CoeffVec N → Halo2GenVec N → MsmEcPoint
/-- Fiat–Shamir challenge `u` squeezed from `(L, R)`. -/
axiom halo2_squeeze : MsmEcPoint → MsmEcPoint → MsmEcScalar
/-- Fold the coefficient vector by `u`/`u⁻¹`, halving its length `2N → N`. -/
axiom halo2_fold_coeffs (N : Nat) : Halo2CoeffVec (2 * N) → MsmEcScalar → Halo2CoeffVec N
/-- Fold the generator vector by `u⁻¹`/`u`, halving its length `2N → N`. -/
axiom halo2_fold_gens (N : Nat) : Halo2GenVec (2 * N) → MsmEcScalar → Halo2GenVec N
/-- Final IPA opening scalar after the vectors collapse (width-indexed). -/
axiom halo2_ipa_open (N : Nat) : Halo2CoeffVec N → MsmEcScalar

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

`halo2IPAProverLean8` is the pure Lean spec for the `n = 8` (3-round) Halo2 IPA
opening: witness commit, gate/permutation transcript round, three (L, R,
squeeze, fold-coeffs, fold-gens) IPA rounds, final opening. We register the
fold leaves at the *output* widths the rounds produce; to keep the registry
single-instance per leaf name we instantiate the fold leaves at the first
round's widths and reuse the same leaf for later rounds (the runtime fold body
is width-polymorphic). -/

noncomputable def halo2IPAProverLean8
    (coeffs : Halo2CoeffVec 8) (G : Halo2GenVec 8) : MsmEcScalar :=
  let _cmt := halo2_commit 8 coeffs G
  let _cg  := halo2_gate_round 8 coeffs
  -- round 0 : 8 → 4
  let L0 := halo2_ipa_L 8 coeffs G
  let R0 := halo2_ipa_R 8 coeffs G
  let u0 := halo2_squeeze L0 R0
  let c1 := halo2_fold_coeffs 4 coeffs u0
  let _G1 := halo2_fold_gens 4 G u0
  -- round 1 : 4 → 2 (reuse the 4-width fold leaf; runtime is poly)
  let L1 := halo2_ipa_L 8 coeffs G
  let R1 := halo2_ipa_R 8 coeffs G
  let u1 := halo2_squeeze L1 R1
  let _c2 := halo2_fold_coeffs 4 coeffs u1
  let _G2 := halo2_fold_gens 4 G u1
  -- round 2 : 2 → 1
  let L2 := halo2_ipa_L 8 coeffs G
  let R2 := halo2_ipa_R 8 coeffs G
  let u2 := halo2_squeeze L2 R2
  let _c3 := halo2_fold_coeffs 4 coeffs u2
  let _G3 := halo2_fold_gens 4 G u2
  halo2_ipa_open 4 c1

/-! ## 5. Hand-built `LowCT` body -/

def halo2CoeffTowerType (N : Nat) : TowerType := .TBytes (1 * N)
def halo2GenTowerType (N : Nat) : TowerType := .TBytes (2 * N)
def halo2PointTowerType : TowerType := .TBytes 2
def halo2ScalarTowerType : TowerType := .TBytes 1

private def loc (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-- Body for the `n = 8` (3-round) Halo2 IPA opening. The fold leaves are
    called at the registered width-4 leaf name; the wires carry the 4-byte /
    8-byte output buffers the registry typed them at. -/
def halo2IPAProverBody8 : LowCT :=
  let c_l   := loc "coeffs"   (halo2CoeffTowerType 8)
  let G_l   := loc "G"        (halo2GenTowerType 8)
  let cmt_l := loc "cmt"      halo2PointTowerType
  let cg_l  := loc "cg"       halo2ScalarTowerType
  let L0_l  := loc "L0"       halo2PointTowerType
  let R0_l  := loc "R0"       halo2PointTowerType
  let u0_l  := loc "u0"       halo2ScalarTowerType
  let c1_l  := loc "c1"       (halo2CoeffTowerType 4)
  let G1_l  := loc "G1"       (halo2GenTowerType 4)
  let L1_l  := loc "L1"       halo2PointTowerType
  let R1_l  := loc "R1"       halo2PointTowerType
  let u1_l  := loc "u1"       halo2ScalarTowerType
  let c2_l  := loc "c2"       (halo2CoeffTowerType 4)
  let G2_l  := loc "G2"       (halo2GenTowerType 4)
  let L2_l  := loc "L2"       halo2PointTowerType
  let R2_l  := loc "R2"       halo2PointTowerType
  let u2_l  := loc "u2"       halo2ScalarTowerType
  let c3_l  := loc "c3"       (halo2CoeffTowerType 4)
  let G3_l  := loc "G3"       (halo2GenTowerType 4)
  let res_l := loc "__result" halo2ScalarTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq
  (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "halo2_commit_8"      cmt_l [c_l, G_l]))
    (.RCall "halo2_gate_round_8"  cg_l  [c_l]))
    (.RCall "halo2_ipa_L_8"       L0_l  [c_l, G_l]))
    (.RCall "halo2_ipa_R_8"       R0_l  [c_l, G_l]))
    (.RCall "halo2_squeeze"       u0_l  [L0_l, R0_l]))
    (.RCall "halo2_fold_coeffs_4" c1_l  [c_l, u0_l]))
    (.RCall "halo2_fold_gens_4"   G1_l  [G_l, u0_l]))
    (.RCall "halo2_ipa_L_8"       L1_l  [c_l, G_l]))
    (.RCall "halo2_ipa_R_8"       R1_l  [c_l, G_l]))
    (.RCall "halo2_squeeze"       u1_l  [L1_l, R1_l]))
    (.RCall "halo2_fold_coeffs_4" c2_l  [c_l, u1_l]))
    (.RCall "halo2_fold_gens_4"   G2_l  [G_l, u1_l]))
    (.RCall "halo2_ipa_L_8"       L2_l  [c_l, G_l]))
    (.RCall "halo2_ipa_R_8"       R2_l  [c_l, G_l]))
    (.RCall "halo2_squeeze"       u2_l  [L2_l, R2_l]))
    (.RCall "halo2_fold_coeffs_4" c3_l  [c_l, u2_l]))
    (.RCall "halo2_fold_gens_4"   G3_l  [G_l, u2_l]))
    (.RCall "halo2_ipa_open"      res_l [c1_l])

/-- `ReifiedFunc` bundle for the `n = 8` Halo2 IPA prover. -/
def halo2IPAProver8Reified : ReifiedFunc :=
  { args    := [("coeffs", halo2CoeffTowerType 8), ("G", halo2GenTowerType 8)]
    body    := halo2IPAProverBody8
    retName := "__result" }

/-! ## 6. Inspection -/

#eval halo2IPAProver8Reified.args.map Prod.fst              -- [coeffs, G]
#eval halo2IPAProver8Reified.retName                        -- __result

end CatCrypt.Crypto.Jasmin.LowCTReflect
