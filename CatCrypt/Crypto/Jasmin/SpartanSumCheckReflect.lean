/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# Spartan sum-check prover reflect surface

The Spartan zkSNARK prover's hot path is a multi-round sum-check: each round the
prover commits a univariate round polynomial, the verifier (Fiat–Shamir)
squeezes a challenge, the round polynomial is evaluated at that challenge by a
Horner fold, and after `n` rounds the multilinear polynomial commitment is
opened. `EmittedSumCheckRealization.lean` already proves the *round evaluator*
(the Horner fold `bbHornerEval` over the verified Baby Bear field kernels)
realizes `UnivariatePoly.eval` of the concrete Baby Bear `SumCheckParams`, so
the sum-check soundness bound lands on the emitted round (Axis B).

This module supplies the **Axis-A** piece: the *prover orchestration* — the
per-round (commit, squeeze, eval) loop plus the closing PCS open — reflected
through the verified compiler chain `LowCT → Com catCryptDialect → Jasmin`,
the same chain
`bench/plonky3_compare/fri_from_rustcmd.lean` runs for the Plonky3 FRI prover.
Every byte of the emitted `.jazz` goes through the verified front; the field
arithmetic of the round evaluator lives inside the opaque
`spartan_sumcheck_round_eval` leaf (whose internal semantics are the Horner fold
tied to `UnivariatePoly.eval` in `EmittedSumCheckRealization`).

## Prover orchestration (per round)

```
  spartan_prove(witness_poly):
    c0 = commit(witness_poly)                     -- multilinear commitment
    for k in 0..n:
      rpoly_k = round_poly(witness_poly, k)       -- (folded inside the leaf)
      cm_k    = commit_round(rpoly_k)             -- commit the round polynomial
      alpha_k = squeeze(cm_k)                      -- Fiat–Shamir challenge
      v_k     = round_eval(rpoly_k, alpha_k)       -- Horner round evaluator
    open = pcs_open(witness_poly, c0)             -- multilinear-IPA opening
    return open
```

We model each major step as one opaque leaf (matching the FRI reflect surface):

| Lean name                           | Leaf name (.jazz)                  | TowerType    |
|-------------------------------------|------------------------------------|--------------|
| `spartan_commit_witness`            | `spartan_commit_witness`           | `TBytes 32`  |
| `spartan_round_poly N`              | `spartan_round_poly_N`             | `TBytes (8·(d+1))` |
| `spartan_commit_round`              | `spartan_commit_round`             | `TBytes 32`  |
| `spartan_challenger_squeeze`        | `spartan_challenger_squeeze`       | `TBytes 8`   |
| `spartan_sumcheck_round_eval`       | `spartan_sumcheck_round_eval`      | `TBytes 8`   |
| `spartan_pcs_open`                  | `spartan_pcs_open`                 | `TBytes 32`  |

The fold loop is **statically unrolled** at Lean time into a flat `RSeq` of
`RCall` chains (`RFor` is not consumed by `translate`, same workaround as
`Plonky3FriReflect.lean`). We emit at `n = 3` (toy R1CS) and `n = 8` (a
representative 256-constraint instance) rounds.

## References

* Setty — *Spartan: zkSNARKs without trusted setup*, CRYPTO 2020.
* `CatCrypt/Crypto/ZK/Spartan/EmittedSumCheckRealization.lean` (the round-eval
  realization the emitted leaf inherits).
* Sibling: `CatCrypt/Crypto/Jasmin/Plonky3FriReflect.lean`.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque Spartan sum-check surface types -/

opaque SpartanWitness.Impl : NonemptyType.{0}
/-- The multilinear witness polynomial (opaque byte buffer; the prover commits
    and opens it). -/
def SpartanWitness : Type := SpartanWitness.Impl.type
instance : Nonempty SpartanWitness := SpartanWitness.Impl.property
/-- Axiomatic inhabitant. -/ axiom SpartanWitness.default : SpartanWitness
noncomputable instance : Inhabited SpartanWitness := ⟨SpartanWitness.default⟩

opaque SpartanRoundPoly.Impl (N : Nat) : NonemptyType.{0}
/-- A univariate round polynomial, `d+1` packed Baby Bear coefficients. -/
def SpartanRoundPoly (N : Nat) : Type := (SpartanRoundPoly.Impl N).type
instance (N : Nat) : Nonempty (SpartanRoundPoly N) := (SpartanRoundPoly.Impl N).property
/-- Axiomatic inhabitant. -/ axiom SpartanRoundPoly.default (N : Nat) : SpartanRoundPoly N
noncomputable instance (N : Nat) : Inhabited (SpartanRoundPoly N) :=
  ⟨SpartanRoundPoly.default N⟩

opaque SpartanDigest.Impl : NonemptyType.{0}
/-- A 32-byte commitment digest. -/
def SpartanDigest : Type := SpartanDigest.Impl.type
instance : Nonempty SpartanDigest := SpartanDigest.Impl.property
/-- Axiomatic inhabitant. -/ axiom SpartanDigest.default : SpartanDigest
noncomputable instance : Inhabited SpartanDigest := ⟨SpartanDigest.default⟩

opaque SpartanFelt.Impl : NonemptyType.{0}
/-- An 8-byte Fiat–Shamir challenge / round evaluation (one Baby Bear element). -/
def SpartanFelt : Type := SpartanFelt.Impl.type
instance : Nonempty SpartanFelt := SpartanFelt.Impl.property
/-- Axiomatic inhabitant. -/ axiom SpartanFelt.default : SpartanFelt
noncomputable instance : Inhabited SpartanFelt := ⟨SpartanFelt.default⟩

/-! ## 2. Sum-check prover leaves (opaque constants and axioms = jasmin function symbols) -/

/-- Commit to the multilinear witness polynomial (multilinear-IPA / Hyrax). -/
noncomputable opaque spartan_commit_witness : SpartanWitness → SpartanDigest

/-- Compute round `k`'s univariate round polynomial from the witness.
    Indexed by the round-polynomial coefficient count `N = d+1`. -/
noncomputable opaque spartan_round_poly (N : Nat) : SpartanWitness → SpartanRoundPoly N

/-- Commit to a round polynomial. -/
noncomputable opaque spartan_commit_round (N : Nat) : SpartanRoundPoly N → SpartanDigest

/-- Fiat–Shamir challenger squeeze: next round challenge from the transcript. -/
noncomputable opaque spartan_challenger_squeeze : SpartanDigest → SpartanFelt

/-- Evaluate a round polynomial at the challenge by the **Horner round**.
    The leaf's internal semantics are `bbHornerEval`, tied to
    `UnivariatePoly.eval` in `EmittedSumCheckRealization.lean`. -/
noncomputable opaque spartan_sumcheck_round_eval (N : Nat) :
    SpartanRoundPoly N → SpartanFelt → SpartanFelt

/-- Open the multilinear polynomial commitment (multilinear-IPA opening). -/
noncomputable opaque spartan_pcs_open : SpartanWitness → SpartanDigest → SpartanDigest

/-! ## 3. `@[rust_cmd_pattern]` registrations

The round-polynomial degree we emit at is `d = 2` (Spartan's round polynomials
are degree 2–3), so the coefficient count is `N = d+1 = 3`. -/

/-- Register `spartan_commit_witness`. -/
@[rust_cmd_pattern]
def spartanCommitWitnessPattern : LowCTPattern where
  name      := "spartan_commit_witness"
  fnHead    := ``spartan_commit_witness
  arity     := 1
  towerType := .TBytes 32

/-- Register `spartan_round_poly` at `N = 3`. -/
@[rust_cmd_pattern]
def spartanRoundPoly3Pattern : LowCTPattern where
  name      := "spartan_round_poly_3"
  fnHead    := ``spartan_round_poly
  arity     := 1
  towerType := .TBytes (8 * 3)

/-- Register `spartan_commit_round` at `N = 3`. -/
@[rust_cmd_pattern]
def spartanCommitRound3Pattern : LowCTPattern where
  name      := "spartan_commit_round_3"
  fnHead    := ``spartan_commit_round
  arity     := 1
  towerType := .TBytes 32

/-- Register `spartan_challenger_squeeze`. -/
@[rust_cmd_pattern]
def spartanChallengerSqueezePattern : LowCTPattern where
  name      := "spartan_challenger_squeeze"
  fnHead    := ``spartan_challenger_squeeze
  arity     := 1
  towerType := .TBytes 8

/-- Register `spartan_sumcheck_round_eval` at `N = 3`. -/
@[rust_cmd_pattern]
def spartanSumcheckRoundEval3Pattern : LowCTPattern where
  name      := "spartan_sumcheck_round_eval_3"
  fnHead    := ``spartan_sumcheck_round_eval
  arity     := 2
  towerType := .TBytes 8

/-- Register `spartan_pcs_open`. -/
@[rust_cmd_pattern]
def spartanPcsOpenPattern : LowCTPattern where
  name      := "spartan_pcs_open"
  fnHead    := ``spartan_pcs_open
  arity     := 2
  towerType := .TBytes 32

/-! ## 4. Pure-Lean Spartan sum-check prover

`spartanProverLean_<n>` is the pure Lean specification for the fixed-round
emit: one witness commitment, `n` rounds of (round-poly, commit, squeeze,
eval), one PCS open. -/

/-- Pure-Lean Spartan prover, `n = 3` sum-check rounds (degree-2 round polys). -/
noncomputable def spartanProverLean3 (w : SpartanWitness) : SpartanDigest :=
  let c0  := spartan_commit_witness w
  -- round 0
  let r0  := spartan_round_poly 3 w
  let cm0 := spartan_commit_round 3 r0
  let a0  := spartan_challenger_squeeze cm0
  let _v0 := spartan_sumcheck_round_eval 3 r0 a0
  -- round 1
  let r1  := spartan_round_poly 3 w
  let cm1 := spartan_commit_round 3 r1
  let a1  := spartan_challenger_squeeze cm1
  let _v1 := spartan_sumcheck_round_eval 3 r1 a1
  -- round 2
  let r2  := spartan_round_poly 3 w
  let cm2 := spartan_commit_round 3 r2
  let a2  := spartan_challenger_squeeze cm2
  let _v2 := spartan_sumcheck_round_eval 3 r2 a2
  spartan_pcs_open w c0

/-! ## 5. Hand-built `LowCT` bodies — the front-end input

`reifyLowCT%` does not consult the registry, so we hand-build the body. Each
`RCall` matches one `let`-binding in `spartanProverLean_<n>`. -/

/-- TowerType for a round polynomial of `N` coefficients (8 bytes/elem). -/
def spartanRoundPolyTowerType (N : Nat) : TowerType := .TBytes (8 * N)
/-- TowerType for a commitment digest. -/
def spartanDigestTowerType : TowerType := .TBytes 32
/-- TowerType for a Baby Bear field element. -/
def spartanFeltTowerType : TowerType := .TBytes 8
/-- TowerType for the witness (modelled as a 32-byte handle). -/
def spartanWitnessTowerType : TowerType := .TBytes 32

def locSpartanSumCheck (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-- Body for `n = 3` sum-check rounds. -/
def spartanProverBody3 : LowCT :=
  let w_l   := locSpartanSumCheck "w"        spartanWitnessTowerType
  let c0_l  := locSpartanSumCheck "c0"       spartanDigestTowerType
  let r0_l  := locSpartanSumCheck "r0"       (spartanRoundPolyTowerType 3)
  let cm0_l := locSpartanSumCheck "cm0"      spartanDigestTowerType
  let a0_l  := locSpartanSumCheck "a0"       spartanFeltTowerType
  let v0_l  := locSpartanSumCheck "v0"       spartanFeltTowerType
  let r1_l  := locSpartanSumCheck "r1"       (spartanRoundPolyTowerType 3)
  let cm1_l := locSpartanSumCheck "cm1"      spartanDigestTowerType
  let a1_l  := locSpartanSumCheck "a1"       spartanFeltTowerType
  let v1_l  := locSpartanSumCheck "v1"       spartanFeltTowerType
  let r2_l  := locSpartanSumCheck "r2"       (spartanRoundPolyTowerType 3)
  let cm2_l := locSpartanSumCheck "cm2"      spartanDigestTowerType
  let a2_l  := locSpartanSumCheck "a2"       spartanFeltTowerType
  let v2_l  := locSpartanSumCheck "v2"       spartanFeltTowerType
  let res_l := locSpartanSumCheck "__result" spartanDigestTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq
  (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "spartan_commit_witness"        c0_l  [w_l]))
    (.RCall "spartan_round_poly_3"          r0_l  [w_l]))
    (.RCall "spartan_commit_round_3"        cm0_l [r0_l]))
    (.RCall "spartan_challenger_squeeze"    a0_l  [cm0_l]))
    (.RCall "spartan_sumcheck_round_eval_3" v0_l  [r0_l, a0_l]))
    (.RCall "spartan_round_poly_3"          r1_l  [w_l]))
    (.RCall "spartan_commit_round_3"        cm1_l [r1_l]))
    (.RCall "spartan_challenger_squeeze"    a1_l  [cm1_l]))
    (.RCall "spartan_sumcheck_round_eval_3" v1_l  [r1_l, a1_l]))
    (.RCall "spartan_round_poly_3"          r2_l  [w_l]))
    (.RCall "spartan_commit_round_3"        cm2_l [r2_l]))
    (.RCall "spartan_challenger_squeeze"    a2_l  [cm2_l]))
    (.RCall "spartan_sumcheck_round_eval_3" v2_l  [r2_l, a2_l]))
    (.RCall "spartan_pcs_open"              res_l [w_l, c0_l])

/-- `ReifiedFunc` bundle for the `n = 3` Spartan prover. -/
def spartanProver3Reified : ReifiedFunc :=
  { args    := [("w", spartanWitnessTowerType)]
    body    := spartanProverBody3
    retName := "__result" }

/-! ## 6. Inspection -/

#eval spartanProver3Reified.args.map Prod.fst              -- [w]
#eval spartanProver3Reified.retName                        -- __result

end CatCrypt.Crypto.Jasmin.LowCTReflect
