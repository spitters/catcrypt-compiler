/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Crypto.Jasmin.LeafSig
public import CatCrypt.Crypto.Jasmin.LeafSig


@[expose] public section
set_option autoImplicit false

/-!
# BLS12-381 G1 multi-scalar-multiplication leaf (AUCurves Pippenger citation)

This module declares the BLS12-381 G1 multi-scalar multiplication
`out = Σ kᵢ · Pᵢ` as a cited leaf for CatCrypt's verified front, following
the `extCall` pattern (`Jasmin.LowCT` `RCall`) and the leaf shape of
`Vale/Bls12381FieldMul.lean`.

The leaf's discharging authority is the AUCurves Bedrock2 Pippenger MSM
program `msm_bls12`, whose correctness theorem `BLS12_MSM.msm_bls12_ok`
(`Qed`) proves the bedrock2 program computes the Gallina reference
`msm_pippenger` (the bucket-method fold). The exact scope of that theorem —
and the residual links between it and this leaf's `Σ kᵢ · Pᵢ` denotation —
is tabulated in the companion `Bls12381MsmCoqAxioms.lean`.

## Timing class: vartime for public scalars

This is the **verifier-side multi-scalar multiplication**, where the
scalars are the public verification-equation coefficients (public inputs,
not secrets). A data-dependent (variable-time) Pippenger bucket method is
therefore admissible: the scalars carry no secret, so there is no
constant-time obligation on them. This leaf makes **no** constant-time
claim. The admissibility of the vartime schedule is the public-scalar
license of the information-flow policy (`ctRelF` treats the scalars as
`Public`), not a CT proof.

## Leaf C signature (extraction wrapper shape)

The AUCurves extraction (`BLS12_MSM_Extract.v`) emits the bedrock2 function
`msm_bls12`, wrapped in Safe Rust as:

```rust
/// out = Σ scalars[i] · points[i] for i in 0..n.
pub fn msm(out: &mut JacobianPoint, scalars: &[Scalar256], points: &[JacobianPoint]);
```

A Jacobian G1 point is 3 × 48 = 144 bytes; a scalar is 4 × u64 = 32 bytes.
Non-aliasing (`out` distinct from `scalars` / `points`) is required by the
bedrock2 spec `spec_of_msm_bls12` and by Rust's borrow checker.

## Provenance and link-time trust

* **Coq proof (the cited authority)**: `BLS12_MSM.msm_bls12_ok` (`Qed`),
  `AUCurves/src/Bedrock/BLS12_MSM.v`. The trust basis is the Coq theorem,
  not the extracted `.rs` / `.jazz`.
* **Symbol identity at link time**: the benched Pippenger and the AUCurves
  `msm_bls12` are two implementations of the same `Σ kᵢ · Pᵢ` spec;
  associating the leaf denotation with the linked symbol is the standard
  C-linker symbol-identity trust story (same as `Bls12381FieldMul`).
-/

namespace CatCrypt.Crypto.Vale.Bls12381Msm

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect

/-! ## §1. Opaque BLS12-381 G1 point type and group operations

A BLS12-381 G1 point (Jacobian coordinates, 3 × 48 = 144 bytes on the
wire). Opaque: the leaf treats G1 addition, the identity, and scalar
multiplication as external operations, matching the abstract `g1_add_spec`
/ `g1_double_spec` / `g1_identity` over which the AUCurves theorem is
parametric. -/
axiom Bls12381G1 : Type

/-- Axiomatic inhabitant. -/
axiom Bls12381G1.default : Bls12381G1
noncomputable instance : Inhabited Bls12381G1 := ⟨Bls12381G1.default⟩

/-- The G1 identity (point at infinity `O`). -/
axiom Bls12381G1.zero : Bls12381G1

/-- G1 point addition `P + Q`. -/
axiom Bls12381G1.add : Bls12381G1 → Bls12381G1 → Bls12381G1

/-- G1 scalar multiplication `k · P`. -/
axiom Bls12381G1.smul : Nat → Bls12381G1 → Bls12381G1

/-! ## §2. Leaf denotation — the naive multi-scalar sum `Σ kᵢ · Pᵢ`

The denotation is the mathematical multi-scalar-multiplication reference:
the sum, over the identity, of the term-wise scalar multiples. This is the
spec the AUCurves Pippenger program is cited to compute. -/

/-- **Leaf denotation**: `Σ kᵢ · Pᵢ`, the multi-scalar sum of `points`
    weighted by `scalars`, folded over the G1 identity. -/
noncomputable def bls12381_g1_msm_denote
    (scalars : List Nat) (points : List Bls12381G1) : Bls12381G1 :=
  (List.zipWith Bls12381G1.smul scalars points).foldr Bls12381G1.add Bls12381G1.zero

/-- The empty MSM is the identity. -/
theorem bls12381_g1_msm_denote_nil :
    bls12381_g1_msm_denote [] [] = Bls12381G1.zero := rfl

/-- One-term unfolding: `Σ` over `(k :: ks, P :: Ps)` is `k·P + Σ`. -/
theorem bls12381_g1_msm_denote_cons (k : Nat) (ks : List Nat)
    (P : Bls12381G1) (Ps : List Bls12381G1) :
    bls12381_g1_msm_denote (k :: ks) (P :: Ps)
      = Bls12381G1.add (Bls12381G1.smul k P) (bls12381_g1_msm_denote ks Ps) := rfl

/-! ## §3. `@[rust_cmd_pattern]` registration

Register `bls12381_g1_msm_denote` → leaf `msm_bls12` (the AUCurves
extraction function name). `reifyLowCT%` does not consult the registry, so
this registration is documentary and the reified body below is hand-built,
following `MsmReflect` / `Bls12381FieldMul`. -/

/-- Register `bls12381_g1_msm_denote` → leaf `msm_bls12`. The destination
    tower type is a 144-byte Jacobian G1 point (3 × 48). -/
@[rust_cmd_pattern]
def bls12381MsmPattern : LowCTPattern where
  name      := "msm_bls12"
  fnHead    := ``bls12381_g1_msm_denote
  arity     := 2
  towerType := .TBytes 144   -- 144-byte Jacobian G1 point (3 × 48)

/-! ## §4. Tower-type abbreviations -/

/-- Tower type of a BLS12-381 G1 point (`TBytes 144`, Jacobian 3 × 48). -/
def bls12381G1TowerType : TowerType := .TBytes 144

/-- Tower type of a BLS12-381 scalar (`TBytes 32`, 4 × u64 LE). -/
def bls12381ScalarTowerType : TowerType := .TBytes 32

/-! ## §5. `LeafSig` entry

The extraction wrapper is non-aliasing: `out` is distinct from `scalars`
and `points` (required by `spec_of_msm_bls12`). `destAliasOk := []`. -/

/-- Per-leaf signature for `msm_bls12`: no aliasing permitted. -/
def bls12381MsmLeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "msm_bls12"
  destAliasOk := []

/-! ## §6. Hand-built `LowCT` body (front-end input)

A single leaf call over the `scalars` and `points` buffers, mirroring the
`Bls12381FieldMul` reified body. The list operands are passed by their
buffer locations. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for the BLS12-381 G1 MSM. Shape:
    `RSeq RSkip (RCall "msm_bls12" __result [scalars, points])`. -/
def bls12381MsmBody : LowCT :=
  let scalars_l := loc "scalars"  bls12381ScalarTowerType
  let points_l  := loc "points"   bls12381G1TowerType
  let result_l  := loc "__result" bls12381G1TowerType
  .RSeq .RSkip
    (.RCall "msm_bls12" result_l [scalars_l, points_l])

/-- `ReifiedFunc` bundle for the AUCurves BLS12-381 G1 MSM leaf. -/
def bls12381MsmReified : ReifiedFunc :=
  { args    := [("scalars", bls12381ScalarTowerType),
                ("points", bls12381G1TowerType)]
    body    := bls12381MsmBody
    retName := "__result" }

/-! ## §7. Inspection -/

#eval bls12381MsmReified.args.map Prod.fst    -- [scalars, points]
#eval bls12381MsmReified.args.length          -- 2
#eval bls12381MsmReified.retName              -- __result

end CatCrypt.Crypto.Vale.Bls12381Msm
