/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# Jolt prover reflect surface

The Jolt zkVM prover's hot path is a sum-check (as in Spartan) *plus* the Lasso
lookup argument, whose core is a grand-product / multiset-fingerprint
`∏_{x ∈ M} (τ − x)`. `Jolt/EmittedSumCheckRealization.lean` already proves the
emitted grand product (`bbGrandProduct`, a `foldr` of `bbMul (bbSub τ x) acc`
over the verified Baby Bear field kernels) realizes `(multisetPoly M).eval τ`,
the evaluator the Lasso multiset-equality soundness bound quantifies over
(Axis B).

This module supplies the **Axis-A** piece: the *prover
orchestration* — sum-check rounds + the Lasso grand-product fingerprint +
commit + PCS open — reflected through the verified compiler chain
`LowCT → Com catCryptDialect → Jasmin`, the same chain
`bench/plonky3_compare/fri_from_rustcmd.lean` runs for the Plonky3 FRI prover.
The field arithmetic of the round evaluator and the grand product lives inside
the opaque `jolt_sumcheck_round_eval` / `jolt_grand_product` leaves, whose
internal semantics are tied to `UnivariatePoly.eval` / `multisetPoly.eval` in
`Jolt/EmittedSumCheckRealization.lean`.

## Prover orchestration

```
  jolt_prove(witness):
    c0 = commit(witness)
    for k in 0..n:                                  -- sum-check rounds
      r_k  = round_poly(witness, k)
      cm_k = commit_round(r_k)
      a_k  = squeeze(cm_k)
      v_k  = round_eval(r_k, a_k)
    -- Lasso lookup argument:
    tau  = squeeze(cm_{n-1})                         -- multiset challenge
    gp   = grand_product(lookups, tau)               -- ∏ (τ − x)
    open = pcs_open(witness, c0)
    return fold_gp(open, gp)                          -- bind proof to multiset
```

The returned digest folds in the Lasso grand-product fingerprint (`out[i] =
open[i] + gp · cᵢ` over Baby Bear), so a multiset/witness-only tamper that
changes `gp` flips the returned proof digest.

We model each major step as one opaque leaf (matching the FRI reflect surface):

| Lean name                        | Leaf name (.jazz)             | TowerType    |
|----------------------------------|-------------------------------|--------------|
| `jolt_commit_witness`            | `jolt_commit_witness`         | `TBytes 32`  |
| `jolt_round_poly N`              | `jolt_round_poly_N`           | `TBytes (8·N)` |
| `jolt_commit_round`              | `jolt_commit_round`           | `TBytes 32`  |
| `jolt_challenger_squeeze`        | `jolt_challenger_squeeze`     | `TBytes 8`   |
| `jolt_sumcheck_round_eval N`     | `jolt_sumcheck_round_eval_N`  | `TBytes 8`   |
| `jolt_grand_product N`           | `jolt_grand_product_N`        | `TBytes 8`   |
| `jolt_pcs_open`                  | `jolt_pcs_open`               | `TBytes 32`  |
| `jolt_fold_gp`                   | `jolt_fold_gp`                | `TBytes 32`  |

The loop is **statically unrolled** at Lean time (`RFor` is not consumed by
`translate`, same workaround as `Plonky3FriReflect.lean`). We emit at `n = 3`
sum-check rounds with a `|M| = 8`-element Lasso grand product.

## References

* Arun, Setty, Thaler — *Jolt: SNARKs for Virtual Machines via Lookups*,
  EUROCRYPT 2024.
* `CatCrypt/Crypto/ZK/Jolt/EmittedSumCheckRealization.lean` (the round-eval +
  grand-product realizations the emitted leaves inherit).
* Sibling: `CatCrypt/Crypto/Jasmin/SpartanSumCheckReflect.lean`.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque Jolt prover surface types -/

opaque JoltWitness.Impl : NonemptyType.{0}
/-- The Jolt witness (execution trace + memory polynomials, opaque handle). -/
def JoltWitness : Type := JoltWitness.Impl.type
instance : Nonempty JoltWitness := JoltWitness.Impl.property
/-- Axiomatic inhabitant. -/ axiom JoltWitness.default : JoltWitness
noncomputable instance : Inhabited JoltWitness := ⟨JoltWitness.default⟩

opaque JoltRoundPoly.Impl (N : Nat) : NonemptyType.{0}
/-- A univariate round polynomial, `N = d+1` packed Baby Bear coefficients. -/
def JoltRoundPoly (N : Nat) : Type := (JoltRoundPoly.Impl N).type
instance (N : Nat) : Nonempty (JoltRoundPoly N) := (JoltRoundPoly.Impl N).property
/-- Axiomatic inhabitant. -/ axiom JoltRoundPoly.default (N : Nat) : JoltRoundPoly N
noncomputable instance (N : Nat) : Inhabited (JoltRoundPoly N) :=
  ⟨JoltRoundPoly.default N⟩

opaque JoltLookups.Impl (N : Nat) : NonemptyType.{0}
/-- The Lasso lookup multiset (opaque buffer of `N` packed elements). -/
def JoltLookups (N : Nat) : Type := (JoltLookups.Impl N).type
instance (N : Nat) : Nonempty (JoltLookups N) := (JoltLookups.Impl N).property
/-- Axiomatic inhabitant. -/ axiom JoltLookups.default (N : Nat) : JoltLookups N
noncomputable instance (N : Nat) : Inhabited (JoltLookups N) :=
  ⟨JoltLookups.default N⟩

opaque JoltDigest.Impl : NonemptyType.{0}
/-- A 32-byte commitment digest. -/
def JoltDigest : Type := JoltDigest.Impl.type
instance : Nonempty JoltDigest := JoltDigest.Impl.property
/-- Axiomatic inhabitant. -/ axiom JoltDigest.default : JoltDigest
noncomputable instance : Inhabited JoltDigest := ⟨JoltDigest.default⟩

opaque JoltFelt.Impl : NonemptyType.{0}
/-- An 8-byte Baby Bear field element (challenge / evaluation / fingerprint). -/
def JoltFelt : Type := JoltFelt.Impl.type
instance : Nonempty JoltFelt := JoltFelt.Impl.property
/-- Axiomatic inhabitant. -/ axiom JoltFelt.default : JoltFelt
noncomputable instance : Inhabited JoltFelt := ⟨JoltFelt.default⟩

/-! ## 2. Jolt prover leaves (opaque constants = jasmin function symbols) -/

/-- Commit to the Jolt witness. -/
noncomputable opaque jolt_commit_witness : JoltWitness → JoltDigest
/-- Compute round `k`'s univariate round polynomial. -/
noncomputable opaque jolt_round_poly (N : Nat) : JoltWitness → JoltRoundPoly N
/-- Commit to a round polynomial. -/
noncomputable opaque jolt_commit_round (N : Nat) : JoltRoundPoly N → JoltDigest
/-- Fiat–Shamir challenger squeeze. -/
noncomputable opaque jolt_challenger_squeeze : JoltDigest → JoltFelt
/-- Evaluate a round polynomial at the challenge (Horner round). -/
noncomputable opaque jolt_sumcheck_round_eval (N : Nat) : JoltRoundPoly N → JoltFelt → JoltFelt
/-- Lasso grand-product fingerprint `∏_{x ∈ M} (τ − x)` over the verified
    field kernels (`bbGrandProduct`, tied to `multisetPoly.eval` in
    `Jolt/EmittedSumCheckRealization.lean`). -/
noncomputable opaque jolt_grand_product (N : Nat) : JoltLookups N → JoltFelt → JoltFelt
/-- Open the polynomial commitment. -/
noncomputable opaque jolt_pcs_open : JoltWitness → JoltDigest → JoltDigest
/-- Fold the Lasso grand-product fingerprint into the proof digest, binding the
    returned proof to the multiset: `out[i] = open[i] + gp · cᵢ` over the
    verified Baby Bear field (distinct nonzero `cᵢ`), injective in `gp` per
    limb. This binds the orchestration output to the grand-product (multiset):
    a multiset-only tamper changes the returned proof. -/
noncomputable opaque jolt_fold_gp : JoltDigest → JoltFelt → JoltDigest

/-! ## 3. `@[rust_cmd_pattern]` registrations (n=3 rounds, |M|=8 lookups) -/

@[rust_cmd_pattern]
def joltCommitWitnessPattern : LowCTPattern where
  name := "jolt_commit_witness"; fnHead := ``jolt_commit_witness
  arity := 1; towerType := .TBytes 32

@[rust_cmd_pattern]
def joltRoundPoly3Pattern : LowCTPattern where
  name := "jolt_round_poly_3"; fnHead := ``jolt_round_poly
  arity := 1; towerType := .TBytes (8 * 3)

@[rust_cmd_pattern]
def joltCommitRound3Pattern : LowCTPattern where
  name := "jolt_commit_round_3"; fnHead := ``jolt_commit_round
  arity := 1; towerType := .TBytes 32

@[rust_cmd_pattern]
def joltChallengerSqueezePattern : LowCTPattern where
  name := "jolt_challenger_squeeze"; fnHead := ``jolt_challenger_squeeze
  arity := 1; towerType := .TBytes 8

@[rust_cmd_pattern]
def joltSumcheckRoundEval3Pattern : LowCTPattern where
  name := "jolt_sumcheck_round_eval_3"; fnHead := ``jolt_sumcheck_round_eval
  arity := 2; towerType := .TBytes 8

@[rust_cmd_pattern]
def joltGrandProduct8Pattern : LowCTPattern where
  name := "jolt_grand_product_8"; fnHead := ``jolt_grand_product
  arity := 2; towerType := .TBytes 8

@[rust_cmd_pattern]
def joltPcsOpenPattern : LowCTPattern where
  name := "jolt_pcs_open"; fnHead := ``jolt_pcs_open
  arity := 2; towerType := .TBytes 32

@[rust_cmd_pattern]
def joltFoldGpPattern : LowCTPattern where
  name := "jolt_fold_gp"; fnHead := ``jolt_fold_gp
  arity := 2; towerType := .TBytes 32

/-! ## 4. Pure-Lean Jolt prover -/

/-- Pure-Lean Jolt prover: `n = 3` sum-check rounds + the Lasso grand-product
    fingerprint over an `|M| = 8` lookup multiset + PCS open. -/
noncomputable def joltProverLean3 (w : JoltWitness) (lk : JoltLookups 8) :
    JoltDigest :=
  let c0  := jolt_commit_witness w
  let r0  := jolt_round_poly 3 w
  let cm0 := jolt_commit_round 3 r0
  let a0  := jolt_challenger_squeeze cm0
  let _v0 := jolt_sumcheck_round_eval 3 r0 a0
  let r1  := jolt_round_poly 3 w
  let cm1 := jolt_commit_round 3 r1
  let a1  := jolt_challenger_squeeze cm1
  let _v1 := jolt_sumcheck_round_eval 3 r1 a1
  let r2  := jolt_round_poly 3 w
  let cm2 := jolt_commit_round 3 r2
  let a2  := jolt_challenger_squeeze cm2
  let _v2 := jolt_sumcheck_round_eval 3 r2 a2
  -- Lasso lookup argument: grand-product fingerprint at the multiset challenge
  let gp   := jolt_grand_product 8 lk a2
  let opn  := jolt_pcs_open w c0
  -- Fold the grand-product into the returned proof digest, so the
  -- orchestration output is cryptographically bound to the lookup multiset.
  jolt_fold_gp opn gp

/-! ## 5. Hand-built `LowCT` body -/

def joltRoundPolyTowerType (N : Nat) : TowerType := .TBytes (8 * N)
def joltLookupsTowerType (N : Nat) : TowerType := .TBytes (8 * N)
def joltDigestTowerType : TowerType := .TBytes 32
def joltFeltTowerType : TowerType := .TBytes 8
def joltWitnessTowerType : TowerType := .TBytes 32

def locJoltProver (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-- Body for `n = 3` sum-check rounds + an `|M| = 8` Lasso grand product. -/
def joltProverBody3 : LowCT :=
  let w_l   := locJoltProver "w"        joltWitnessTowerType
  let lk_l  := locJoltProver "lk"       (joltLookupsTowerType 8)
  let c0_l  := locJoltProver "c0"       joltDigestTowerType
  let r0_l  := locJoltProver "r0"       (joltRoundPolyTowerType 3)
  let cm0_l := locJoltProver "cm0"      joltDigestTowerType
  let a0_l  := locJoltProver "a0"       joltFeltTowerType
  let v0_l  := locJoltProver "v0"       joltFeltTowerType
  let r1_l  := locJoltProver "r1"       (joltRoundPolyTowerType 3)
  let cm1_l := locJoltProver "cm1"      joltDigestTowerType
  let a1_l  := locJoltProver "a1"       joltFeltTowerType
  let v1_l  := locJoltProver "v1"       joltFeltTowerType
  let r2_l  := locJoltProver "r2"       (joltRoundPolyTowerType 3)
  let cm2_l := locJoltProver "cm2"      joltDigestTowerType
  let a2_l  := locJoltProver "a2"       joltFeltTowerType
  let v2_l  := locJoltProver "v2"       joltFeltTowerType
  let gp_l  := locJoltProver "gp"       joltFeltTowerType
  let open_l := locJoltProver "open"    joltDigestTowerType
  let res_l := locJoltProver "__result" joltDigestTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq
  (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "jolt_commit_witness"        c0_l  [w_l]))
    (.RCall "jolt_round_poly_3"          r0_l  [w_l]))
    (.RCall "jolt_commit_round_3"        cm0_l [r0_l]))
    (.RCall "jolt_challenger_squeeze"    a0_l  [cm0_l]))
    (.RCall "jolt_sumcheck_round_eval_3" v0_l  [r0_l, a0_l]))
    (.RCall "jolt_round_poly_3"          r1_l  [w_l]))
    (.RCall "jolt_commit_round_3"        cm1_l [r1_l]))
    (.RCall "jolt_challenger_squeeze"    a1_l  [cm1_l]))
    (.RCall "jolt_sumcheck_round_eval_3" v1_l  [r1_l, a1_l]))
    (.RCall "jolt_round_poly_3"          r2_l  [w_l]))
    (.RCall "jolt_commit_round_3"        cm2_l [r2_l]))
    (.RCall "jolt_challenger_squeeze"    a2_l  [cm2_l]))
    (.RCall "jolt_sumcheck_round_eval_3" v2_l  [r2_l, a2_l]))
    (.RCall "jolt_grand_product_8"       gp_l  [lk_l, a2_l]))
    (.RCall "jolt_pcs_open"              open_l [w_l, c0_l]))
    (.RCall "jolt_fold_gp"               res_l [open_l, gp_l])

/-- `ReifiedFunc` bundle for the `n = 3` Jolt prover. Two args: witness + the
    Lasso lookup multiset. -/
def joltProver3Reified : ReifiedFunc :=
  { args    := [("w", joltWitnessTowerType), ("lk", joltLookupsTowerType 8)]
    body    := joltProverBody3
    retName := "__result" }

/-! ## 6. Inspection -/

#eval joltProver3Reified.args.map Prod.fst              -- [w, lk]
#eval joltProver3Reified.retName                        -- __result

end CatCrypt.Crypto.Jasmin.LowCTReflect
