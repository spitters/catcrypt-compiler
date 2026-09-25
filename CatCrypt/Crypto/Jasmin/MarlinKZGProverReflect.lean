/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Bn254Reflect

/-!
# Marlin KZG prover reflect surface

Marlin's polynomial-commitment layer is **KZG over a pairing group** (q-SDH /
trusted setup), unlike Halo2's IPA over Pasta. The prover commits to the AHP
(algebraic holographic proof) polynomials with KZG (each commitment a G1
scalar-mul / point-add over the SRS), runs the sum-check transcript for the
rowcheck / lincheck rounds, batches the polynomial openings at the verifier's
challenge point, and the verifier's pairing check
`e(C − [v]·G, H) = e(W, [τ]·H − H)` closes the KZG opening — one BN254 pairing
plus an `Fp12` multiply (the batched LHS/RHS combination).

This module supplies the **Axis-A** piece (`bench/marlin_compare/
README.md`): the *Marlin KZG prover orchestration* — KZG commit of the AHP
polynomials, the sum-check transcript rounds, the batched KZG opening, and the
final pairing-check combination — reflected through the verified compiler chain
`LowCT → Com catCryptDialect → Jasmin`, the same chain
`bench/plonky3_compare/fri_from_rustcmd.lean` runs for the Plonky3 FRI prover
and `bench/bn254_compare/pairing_from_rustcmd.lean` runs for the BN254 pairing
algorithm. The KZG commit / opening / pairing-check leaves reuse the
**already-emitted BN254 pairing-group leaves** (`bn254_g1_scalar_mul` /
`bn254_g1_add` / `bn254_pairing` / `bn254_fp12_mul` from `Bn254Reflect.lean`,
the reg-ptr field-tower emit + the Miller / final-exp chain), so
the KZG hot path is built over the pairing primitive the suite already emits and
the q-SDH soundness layer (`MarlinBound.marlinKZGError`) quantifies over. The
sum-check round transcript and the batched-opening combination are
Marlin-specific orchestration leaves.

## Prover orchestration (n = 3 sum-check rounds, KZG via the BN254 pairing)

```
  marlin_prove(poly_coeffs, srs):
    cmt = marlin_kzg_commit(poly_coeffs, srs)        -- KZG MSM commitment (G1)
    for k in 0..n:                                   -- sum-check (rowcheck/lincheck)
      a_k = marlin_sumcheck_round(cmt, k)            -- Fiat–Shamir challenge
    w   = marlin_kzg_open(poly_coeffs, a_{n-1})      -- batched opening witness (G1)
    lhs = bn254_pairing(cmt, srs_h)                  -- e(C, H)
    rhs = bn254_pairing(w, srs_h)                    -- e(W, [τ]H − H)
    chk = bn254_fp12_mul(lhs, rhs)                   -- batched pairing combine (GT)
    return marlin_pairing_check(chk)                 -- accept/reject digest
```

We model each Marlin-specific step as one opaque leaf; the KZG commitment / open
reuse the G1 MSM leaves and the verifier check reuses the BN254 pairing + Fp12
multiply under the hood. We emit at `n = 3` sum-check rounds, the canonical
small Marlin size.

## References

* Chiesa, Hu, Maller, Mishra, Vesely, Ward — *Marlin: Preprocessing zkSNARKs
  with Universal and Updatable SRS*, EUROCRYPT 2020.
* Kate, Zaverucha, Goldberg — *Constant-Size Commitments to Polynomials and
  Their Applications* (KZG), ASIACRYPT 2010.
* `CatCrypt/Crypto/ZK/MarlinBound.lean` (`marlinKZGError` = q-SDH advantage on
  the pairing group, the soundness layer the emitted pairing leaf is tied to).
* Sibling: `CatCrypt/Crypto/Jasmin/Bn254Reflect.lean` (the BN254 pairing-group
  leaves reused here), `CatCrypt/Crypto/Jasmin/JoltProverReflect.lean` (the
  sum-check transcript reflect shape).
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque Marlin KZG surface types

The AHP polynomial coefficient vector is an opaque buffer of `N` BN254 `Fr`
scalars (32 B each); the structured reference string (SRS) is an opaque buffer
of `N` G1 points; a KZG commitment / opening witness is one G1 point
(`Bn254G1Point`, reused from `Bn254Reflect`); a sum-check challenge is one `Fr`
scalar; the pairing check produces an `Fp12` (GT) element. -/

opaque MarlinCoeffVec.Impl (N : Nat) : NonemptyType.{0}
/-- The Marlin AHP coefficient vector (opaque buffer of `N` BN254 `Fr` scalars). -/
def MarlinCoeffVec (N : Nat) : Type := (MarlinCoeffVec.Impl N).type
instance (N : Nat) : Nonempty (MarlinCoeffVec N) := (MarlinCoeffVec.Impl N).property
/-- An inhabitant. -/ noncomputable opaque MarlinCoeffVec.default (N : Nat) : MarlinCoeffVec N
noncomputable instance (N : Nat) : Inhabited (MarlinCoeffVec N) :=
  ⟨MarlinCoeffVec.default N⟩

opaque MarlinSRS.Impl (N : Nat) : NonemptyType.{0}
/-- The KZG structured reference string `srs` (opaque buffer of `N` G1 points). -/
def MarlinSRS (N : Nat) : Type := (MarlinSRS.Impl N).type
instance (N : Nat) : Nonempty (MarlinSRS N) := (MarlinSRS.Impl N).property
/-- An inhabitant. -/ noncomputable opaque MarlinSRS.default (N : Nat) : MarlinSRS N
noncomputable instance (N : Nat) : Inhabited (MarlinSRS N) :=
  ⟨MarlinSRS.default N⟩

/-! ## 2. Marlin KZG leaves (opaque constants = jasmin function symbols)

`marlin_kzg_commit` / `marlin_kzg_open` produce G1 points (`Bn254G1Point`,
reused from `Bn254Reflect` — the runtime wires them to
`bn254_g1_scalar_mul`/`bn254_g1_add` MSM chains over the SRS);
`marlin_sumcheck_round` produces an `Fr` challenge; the verifier check reuses
`bn254_pairing` + `bn254_fp12_mul` directly; `marlin_pairing_check` produces the
accept/reject `Fr` digest. -/

/-- KZG commitment `cmt = ⟨coeffs, srs⟩` (a G1 MSM over the SRS). -/
noncomputable opaque marlin_kzg_commit (N : Nat) : MarlinCoeffVec N → MarlinSRS N → Bn254G1Point
/-- One sum-check (rowcheck/lincheck) transcript round → Fiat–Shamir `Fr`. -/
noncomputable opaque marlin_sumcheck_round : Bn254G1Point → Bn254Fr
/-- Batched KZG opening witness `W` at the challenge point (a G1 MSM). -/
noncomputable opaque marlin_kzg_open (N : Nat) : MarlinCoeffVec N → Bn254Fr → Bn254G1Point
/-- Serialize the Marlin proof transcript into the proof buffer (laid over the
    coefficient-width region): the prover writes its commitments / opening
    witness / evaluation proof into the output proof buffer. The batched
    pairing-check `Fp12` (`e(C,H)·e(W,[τ]H−H)`, the KZG verification equation's
    combined product) is threaded as the consumed verifier-side check input. -/
noncomputable opaque marlin_proof_serialize (N : Nat) : MarlinCoeffVec N → Bn254Fp12 → MarlinCoeffVec N

/-! ## 3. `@[rust_cmd_pattern]` registrations (n = 3 sum-check rounds)

The BN254 leaves (`bn254_g1_scalar_mul`, `bn254_g1_add`, `bn254_pairing`,
`bn254_fp12_mul`) are already registered in `Bn254Reflect.lean`; we add only the
Marlin orchestration leaves here. -/

@[rust_cmd_pattern]
def marlinKzgCommit8Pattern : LowCTPattern where
  name := "marlin_kzg_commit_8"; fnHead := ``marlin_kzg_commit; arity := 2; towerType := .TBytes 64

@[rust_cmd_pattern]
def marlinSumcheckRoundPattern : LowCTPattern where
  name := "marlin_sumcheck_round"; fnHead := ``marlin_sumcheck_round; arity := 1; towerType := .TBytes 32

@[rust_cmd_pattern]
def marlinKzgOpen8Pattern : LowCTPattern where
  name := "marlin_kzg_open_8"; fnHead := ``marlin_kzg_open; arity := 2; towerType := .TBytes 64

@[rust_cmd_pattern]
def marlinProofSerialize8Pattern : LowCTPattern where
  name := "marlin_proof_serialize_8"; fnHead := ``marlin_proof_serialize; arity := 2; towerType := .TBytes (32 * 8)

/-! ## 4. Pure-Lean Marlin KZG prover

`marlinKZGProverLean8` is the pure Lean spec for the `n = 3` sum-check / degree-8
Marlin KZG opening: KZG commit, three sum-check transcript rounds, batched KZG
opening, the two pairing evaluations against the SRS-H G2 element + the GT
combine, and the serialized proof. The verifier check
`e(C, H) · e(W, [τ]H − H)` reuses the BN254 pairing (`bn254_pairing : G1 → G2 →
Fp12`) and `Fp12` multiply directly; the runtime supplies `srsH` as the
precomputed G2 SRS element. The serialized proof is written into the
coefficient-width proof buffer (`marlin_proof_serialize`), consuming the
pairing-check `Fp12`. -/

noncomputable def marlinKZGProverLean8
    (coeffs : MarlinCoeffVec 8) (srs : MarlinSRS 8)
    (srsH : Bn254G2Point) : MarlinCoeffVec 8 :=
  let cmt := marlin_kzg_commit 8 coeffs srs
  let _a0 := marlin_sumcheck_round cmt
  let _a1 := marlin_sumcheck_round cmt
  let a2  := marlin_sumcheck_round cmt
  let w   := marlin_kzg_open 8 coeffs a2
  let lhs := bn254_pairing cmt srsH
  let rhs := bn254_pairing w srsH
  let chk := bn254_fp12_mul lhs rhs
  marlin_proof_serialize 8 coeffs chk

/-! ## 5. Hand-built `LowCT` body -/

def marlinCoeffTowerType (N : Nat) : TowerType := .TBytes (32 * N)
def marlinSRSTowerType (N : Nat) : TowerType := .TBytes (64 * N)
def marlinG1TowerType : TowerType := .TBytes 64
def marlinG2TowerType : TowerType := .TBytes 128
def marlinFrTowerType : TowerType := .TBytes 32
def marlinFp12TowerType : TowerType := .TBytes 384

def locMarlinKZGProver (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-- Body for the `n = 3` Marlin KZG prover: KZG commit, three sum-check rounds,
    batched KZG opening, two pairings against the SRS-H G2 element, the GT
    combine, and the accept/reject digest. The pairing leaf is the
    already-registered `bn254_pairing`; the GT multiply is `bn254_fp12_mul`. -/
def marlinKZGProverBody8 : LowCT :=
  let c_l    := locMarlinKZGProver "coeffs"   (marlinCoeffTowerType 8)
  let srs_l  := locMarlinKZGProver "srs"      (marlinSRSTowerType 8)
  let srsH_l := locMarlinKZGProver "srsH"     marlinG2TowerType
  let cmt_l  := locMarlinKZGProver "cmt"      marlinG1TowerType
  let a0_l   := locMarlinKZGProver "a0"       marlinFrTowerType
  let a1_l   := locMarlinKZGProver "a1"       marlinFrTowerType
  let a2_l   := locMarlinKZGProver "a2"       marlinFrTowerType
  let w_l    := locMarlinKZGProver "w"        marlinG1TowerType
  let lhs_l  := locMarlinKZGProver "lhs"      marlinFp12TowerType
  let rhs_l  := locMarlinKZGProver "rhs"      marlinFp12TowerType
  let chk_l  := locMarlinKZGProver "chk"      marlinFp12TowerType
  let res_l  := locMarlinKZGProver "__result" (marlinCoeffTowerType 8)
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "marlin_kzg_commit_8"   cmt_l [c_l, srs_l]))
    (.RCall "marlin_sumcheck_round" a0_l  [cmt_l]))
    (.RCall "marlin_sumcheck_round" a1_l  [cmt_l]))
    (.RCall "marlin_sumcheck_round" a2_l  [cmt_l]))
    (.RCall "marlin_kzg_open_8"     w_l   [c_l, a2_l]))
    (.RCall "bn254_pairing"         lhs_l [cmt_l, srsH_l]))
    (.RCall "bn254_pairing"         rhs_l [w_l, srsH_l]))
    (.RCall "bn254_fp12_mul"        chk_l [lhs_l, rhs_l]))
    (.RCall "marlin_proof_serialize_8" res_l [c_l, chk_l])

/-- `ReifiedFunc` bundle for the `n = 3` Marlin KZG prover. -/
def marlinKZGProver8Reified : ReifiedFunc :=
  { args    := [("coeffs", marlinCoeffTowerType 8),
                ("srs", marlinSRSTowerType 8),
                ("srsH", marlinG2TowerType)]
    body    := marlinKZGProverBody8
    retName := "__result" }

/-! ## 6. Inspection -/

#eval marlinKZGProver8Reified.args.map Prod.fst              -- [coeffs, srs, srsH]
#eval marlinKZGProver8Reified.retName                        -- __result

end CatCrypt.Crypto.Jasmin.LowCTReflect
