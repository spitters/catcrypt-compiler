/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.RustEmit
public import CatCrypt.Crypto.Jasmin.LowCTToJasmin

/-!
# P-384 reflect surface — scalar-mul MSM and ECDSA-verify orchestration

The P-384 (NIST FIPS 186-4) analogue of `P256Reflect.lean`: opaque surface
types (`P384Scalar`, `P384Point`), `@[rust_cmd_pattern]` registrations for the
group-law leaves, hand-built `LowCT` bodies for the two kernels, and Rust
source emission for the shim crate.

## Two kernels

* `p384MsmTermLean` — one term of a multi-scalar multiplication,
  `p384_scalar_mul(k, P)`.
* `p384EcdsaVerifyLean` — the ECDSA-P384 verify orchestration
  `R' = u₁·G + u₂·Q`: two `p384_scalar_mul` leaves and one `p384_point_add`
  leaf.

## Wire encoding

The encoding is that of the Rust crate the leaves are implemented over,
`AUCurves/p384-safe-rust`.

* A scalar is `&[u64; 6]` in `group.rs` `g1_scalar_mul`, i.e. six
  little-endian 64-bit limbs — `TBytes 48`.
* A point is the projective triple `G1 { x, y, z }` of `group.rs`, serialised
  by `wnaf.rs` `point_to_bytes` as `X ‖ Y ‖ Z` at offsets `0`, `48`, `96`,
  each field element six little-endian limbs in Montgomery form — `TBytes 144`.
  `point_from_bytes` is its inverse.

The P-256 file uses a 64-byte affine point (`x ‖ y`). No crate in this
workspace implements that surface, so the P-384 point type is projective and
144 bytes rather than a width-scaled copy of the P-256 one.

## Emitted-signature conventions

The shim crate must match two conventions that differ in argument order.

* `ppRustFunction` emits the function signature with the inputs first, each as
  `&T`, and the outputs last, each as `&mut T`.
* A body-level `.RCall f dest args` emits `f(dest, args…)`, with the
  destination first.

So `p384_ecdsa_verify_msm` has signature
`(u1 : &[u8; 48], G : &[u8; 144], u2 : &[u8; 48], Q : &[u8; 144],
  __result : &mut [u8; 144])`, while the leaf calls inside it read
`p384_scalar_mul(&mut t1, u1, G)`.

## Scope of the claims

The theorems below are structural: the front lowers each body to a Jasmin
command of a stated length whose calls carry the stated leaf names.

The bodies contain `RCall` nodes, so `LowCTToJasmin.rustExecSimulates`, whose
hypothesis is `callFree c = true`, does not apply to them. The applicable
statement is `LowCTToJasmin.rustExecSimulates_withCalls`, which replaces that
hypothesis with `callFreePlusCall c = true` and takes leaf oracles
`hLeafN : ∀ fuel' ≥ 2, LeafImplOkNewSid leafSpec env fuel'` together with
`hLimb` and `hClone`. Instantiating it for these kernels requires a
`LeafSpec` and a `TransEnv` in which `p384_scalar_mul` and `p384_point_add`
are implemented and agree; neither is supplied here, and the leaves are
axioms.

No constant-time property and no security property is claimed. The leaves are
opaque, and the only P-384 `GroupParam` in this workspace is degenerate.

## References

* FIPS 186-4, Appendix D.1.2.4 (P-384)
* `AUCurves/p384-safe-rust`: `group.rs` (`G1`, `g1_add`, `g1_scalar_mul`),
  `wnaf.rs` (`point_to_bytes`, `point_from_bytes`)
* `CatCrypt/Crypto/Jasmin/P256Reflect.lean` — the P-256 sibling
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque P-384 surface types -/

/-- A P-384 scalar, an element of `Fn` modulo the P-384 group order. Six
    little-endian 64-bit limbs, 48 bytes on the wire. Opaque. -/
axiom P384Scalar : Type
/-- Axiomatic inhabitant. -/ axiom P384Scalar.default : P384Scalar
noncomputable instance : Inhabited P384Scalar := ⟨P384Scalar.default⟩

/-- A P-384 projective point `X ‖ Y ‖ Z`, three Montgomery-form base-field
    elements of 48 bytes each, 144 bytes on the wire. Opaque. -/
axiom P384Point : Type
/-- Axiomatic inhabitant. -/ axiom P384Point.default : P384Point
noncomputable instance : Inhabited P384Point := ⟨P384Point.default⟩

/-! ## 2. P-384 leaves -/

/-- P-384 scalar multiplication `R = k · P`. Opaque; the shim issues the
    windowed ladder of `p384-safe-rust` `g1_scalar_mul`. -/
axiom p384_scalar_mul : P384Scalar → P384Point → P384Point

/-- P-384 fixed-base scalar multiplication `R = k · G`, with `G` the P-384
    generator of FIPS 186-4 D.1.2.4. The generator is fixed in the leaf, so a
    caller passes only the scalar.

    Requirements on the implementation: it computes `k · G` for the standard
    generator; it is constant time in `k`, its execution time and memory-access
    trace depending on neither the value of `k` nor the table entries it
    selects; and the precomputed multiples of `G` it reads are for that same
    generator. Opaque here. -/
axiom p384_scalar_mul_base : P384Scalar → P384Point

/-- P-384 point addition `R = P + Q`. Opaque; the shim issues the complete
    projective addition of `p384-safe-rust` `g1_add`. -/
axiom p384_point_add : P384Point → P384Point → P384Point

/-! ## 3. Tower-type abbreviations -/

/-- Tower type of a P-384 scalar: six little-endian 64-bit limbs. -/
def p384ScalarTowerType : TowerType := .TBytes 48

/-- Tower type of a P-384 projective point: `X ‖ Y ‖ Z`, 48 bytes each. -/
def p384PointTowerType : TowerType := .TBytes 144

/-! ## 4. `@[rust_cmd_pattern]` registrations -/

/-- Register `p384_scalar_mul` → leaf `p384_scalar_mul`. -/
@[rust_cmd_pattern]
def p384ScalarMulPattern : LowCTPattern where
  name      := "p384_scalar_mul"
  fnHead    := ``p384_scalar_mul
  arity     := 2
  towerType := .TBytes 144

/-- Register `p384_scalar_mul_base` → leaf `p384_scalar_mul_base`.

    `LowCTPattern` carries a single `towerType` for the destination and every
    argument, and this leaf is heterogeneous (`48 → 144`). The registration
    therefore pins the leaf name, the Lean head `p384_scalar_mul_base`, the
    arity `1`, and the 144-byte destination width; it does not pin the 48-byte
    width of the scalar argument, which the hand-built bodies fix through the
    tower type of the slot they pass. -/
@[rust_cmd_pattern]
def p384ScalarMulBasePattern : LowCTPattern where
  name      := "p384_scalar_mul_base"
  fnHead    := ``p384_scalar_mul_base
  arity     := 1
  towerType := .TBytes 144

/-- Register `p384_point_add` → leaf `p384_point_add`. -/
@[rust_cmd_pattern]
def p384PointAddPattern : LowCTPattern where
  name      := "p384_point_add"
  fnHead    := ``p384_point_add
  arity     := 2
  towerType := .TBytes 144

/-- A `Located` slot in the P-384 kernels. -/
def locP384 (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean kernel specifications -/

/-- One MSM term: `t = p384_scalar_mul(k, P)`. -/
noncomputable def p384MsmTermLean (k : P384Scalar) (P : P384Point) : P384Point :=
  p384_scalar_mul k P

/-- The ECDSA-P384-verify orchestration `R' = u₁·G + u₂·Q`. -/
noncomputable def p384EcdsaVerifyLean
    (u1 : P384Scalar) (G : P384Point)
    (u2 : P384Scalar) (Q : P384Point) : P384Point :=
  p384_point_add (p384_scalar_mul u1 G) (p384_scalar_mul u2 Q)

/-! ## 6. Hand-built `LowCT` bodies -/

/-- The `LowCT` body for one MSM term: a single `p384_scalar_mul` leaf call
    writing `__result`. -/
def p384MsmTermBody : LowCT :=
  let k_l      := locP384 "k"        p384ScalarTowerType
  let P_l      := locP384 "P"        p384PointTowerType
  let result_l := locP384 "__result" p384PointTowerType
  .RCall "p384_scalar_mul" result_l [k_l, P_l]

/-- `ReifiedFunc` bundle for the MSM-term kernel. -/
def p384MsmTermReified : ReifiedFunc :=
  { args    := [("k", p384ScalarTowerType),
                ("P", p384PointTowerType)]
    body    := p384MsmTermBody
    retName := "__result" }

/-- The `LowCT` body for the ECDSA-verify orchestration: two accumulator
    locals, two `p384_scalar_mul` leaf calls and one `p384_point_add` leaf
    call writing `__result`. -/
def p384EcdsaVerifyBody : LowCT :=
  let u1_l     := locP384 "u1"       p384ScalarTowerType
  let G_l      := locP384 "G"        p384PointTowerType
  let u2_l     := locP384 "u2"       p384ScalarTowerType
  let Q_l      := locP384 "Q"        p384PointTowerType
  let t1_l     := locP384 "t1"       p384PointTowerType
  let t2_l     := locP384 "t2"       p384PointTowerType
  let result_l := locP384 "__result" p384PointTowerType
  .RLetZero "t1" p384PointTowerType
    (.RLetZero "t2" p384PointTowerType
      (.RSeq (.RSeq
        (.RCall "p384_scalar_mul" t1_l [u1_l, G_l])
        (.RCall "p384_scalar_mul" t2_l [u2_l, Q_l]))
        (.RCall "p384_point_add" result_l [t1_l, t2_l])))

/-- `ReifiedFunc` bundle for the ECDSA-verify kernel. -/
def p384EcdsaVerifyReified : ReifiedFunc :=
  { args    := [("u1", p384ScalarTowerType),
                ("G",  p384PointTowerType),
                ("u2", p384ScalarTowerType),
                ("Q",  p384PointTowerType)]
    body    := p384EcdsaVerifyBody
    retName := "__result" }

/-! ## 7. Rust emission -/

/-- Rust source for the MSM-term kernel. -/
def p384MsmTermRust : String :=
  ppRustFunction "p384_msm_term"
    [locP384 "k" p384ScalarTowerType,
     locP384 "P" p384PointTowerType]
    [locP384 "__result" p384PointTowerType]
    p384MsmTermBody

/-- Rust source for the ECDSA-verify orchestration. -/
def p384EcdsaVerifyRust : String :=
  ppRustFunction "p384_ecdsa_verify_msm"
    [locP384 "u1" p384ScalarTowerType,
     locP384 "G"  p384PointTowerType,
     locP384 "u2" p384ScalarTowerType,
     locP384 "Q"  p384PointTowerType]
    [locP384 "__result" p384PointTowerType]
    p384EcdsaVerifyBody

/-- Write both Rust kernels into `bench/p384_ecdsa_rust/gen`. -/
def emitP384Rust : IO Unit := do
  IO.FS.createDirAll "bench/p384_ecdsa_rust/gen"
  IO.FS.writeFile
    "bench/p384_ecdsa_rust/gen/p384_ecdsa_verify_msm.rs" p384EcdsaVerifyRust
  IO.println "wrote bench/p384_ecdsa_rust/gen/p384_ecdsa_verify_msm.rs"
  IO.FS.writeFile
    "bench/p384_ecdsa_rust/gen/p384_msm_term.rs" p384MsmTermRust
  IO.println "wrote bench/p384_ecdsa_rust/gen/p384_msm_term.rs"

/-! ## 8. Structural lowering through the front -/

/-- The MSM-term body, lowered through the owned front. -/
def p384MsmTermJasmin := toJasminCmd p384MsmTermBody

/-- The ECDSA-verify body, lowered through the owned front. -/
def p384EcdsaVerifyJasmin := toJasminCmd p384EcdsaVerifyBody

/-- The callee name of a Jasmin instruction, or `none` for a non-call. -/
def jasminCallName : CatCrypt.Crypto.Jasmin.InstrR → Option String
  | .Ccall _ _ fn _ => some fn.name
  | _ => none

/-- The MSM-term body lowers to a one-instruction Jasmin call program. -/
theorem p384MsmTermJasmin_length : p384MsmTermJasmin.length = 1 := rfl

/-- The single instruction the front emits for the MSM term is a `Ccall`. -/
theorem p384MsmTermJasmin_all_calls :
    p384MsmTermJasmin.all (fun i => match i with | .Ccall .. => true | _ => false) = true :=
  rfl

/-- The one call of the MSM term targets the `p384_scalar_mul` leaf. -/
theorem p384MsmTermJasmin_leaf_names :
    p384MsmTermJasmin.filterMap jasminCallName = ["p384_scalar_mul"] := rfl

/-- The ECDSA-verify body lowers to five Jasmin instructions: two local
    array initialisers and three leaf calls. -/
theorem p384EcdsaVerifyJasmin_length : p384EcdsaVerifyJasmin.length = 5 := rfl

/-- The three calls the front emits for the ECDSA-verify body target the two
    `p384_scalar_mul` leaves and the `p384_point_add` leaf, in that order. -/
theorem p384EcdsaVerifyJasmin_leaf_names :
    p384EcdsaVerifyJasmin.filterMap jasminCallName =
      ["p384_scalar_mul", "p384_scalar_mul", "p384_point_add"] := rfl

/-- Every instruction the front emits for the ECDSA-verify body is either a
    local initialiser or a leaf call: the body is fully lowered, with no
    fall-through to an unhandled construct. -/
theorem p384EcdsaVerifyJasmin_all_assgn_or_call :
    p384EcdsaVerifyJasmin.all
      (fun i => match i with
        | .Ccall .. => true
        | .Cassgn .. => true
        | _ => false) = true := rfl

/-! ## 9. Inspection -/

#eval p384MsmTermReified.args.map Prod.fst              -- [k, P]
#eval p384EcdsaVerifyReified.args.map Prod.fst          -- [u1, G, u2, Q]

end CatCrypt.Crypto.Jasmin.LowCTReflect
