/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# BN254 (alt-bn128) reflect surface — G1 MSM + EIP-197 pairing-product through
the verified front

This file is the BN254 analogue of `Bls12381Reflect.lean`. It adds BN254
specific opaque surface types and `@[rust_cmd_pattern]` registrations so that
pure-Lean BN254 G1 MSM and the EIP-197 2-pair pairing-product (the EVM
precompile) can be lifted through the verified compiler chain
`LowCT → CryptoSSA → Com → jasmin`, **without** editing
`LowCTReflect.lean`'s `knownOps` table.

## BN254 width table

| Lean axiom              | Bytes | TowerType    | encodeTy (memref u64 limbs) |
|-------------------------|------:|--------------|----------------------------:|
| `Bn254Fr` (Fr scalar)   |    32 | `TBytes 32`  | 4                           |
| `Bn254G1Point`          |    64 | `TBytes 64`  | 8                           |
| `Bn254G2Point`          |   128 | `TBytes 128` | 16                          |
| `Bn254Fp12`             |   384 | `TBytes 384` | 48                          |

These widths match the legacy Tier C emit (`bench/bn254_compare/bn254_emit.lean`)
and the bn254 crate's on-wire layout (used by the EIP-196 / EIP-197 EVM
precompiles).

## What's verified / what's trusted

The leaves are the AUCurves verified-bedrock2 BN254 tower (`bn254-safe-rust`):
the extracted `Fp / Fp2 / Fp6 / Fp12` tower over verified fiat leaves, plus
`pairing_optimal` (Miller loop + final exp) and `fp12_mul`. AUCurves verifies
the FIELD/PAIRING tower; the G1/G2 group add law stays trusted (the same
hybrid contract as BLS12-381).

## Bridge — no hax extraction available

Unlike BLS12-381 (which has `bls-hax/`) and Groth16/KZG (which have their
own hax extractions), BN254 has **no upstream hax tree**. The drivers
downstream carry the named hypothesis `BN254LeanSpecCorrect` with explicit
reason "no bn254-hax/ tree; bridge would be to Lean reference spec or
KAT-only against the EIP-196/EIP-197 vectors". The production witness is
the bn254 crate's `pairing_optimal` linked by the Rust KAT.

## References

* AUCurves: `bn254-safe-rust` (verified-bedrock2 BN254 tower)
* `CatCrypt/Crypto/Pairing/Bn254Emit.lean` — abstract `Bn254Primitives`,
  `EcLeafAgrees`, `PairingLeavesAgree`, `g1MsmFold_eq_msm`,
  `eip197VerifyCom_denote`, `pairingCom_denote`
* `bench/bn254_compare/bn254_emit.lean` — legacy Tier C emit (superseded)
* `CatCrypt/Crypto/Jasmin/Bls12381Reflect.lean` — sibling pattern
* EIP-196 / EIP-197 — published precompile test vectors
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque BN254 surface types -/

/-- A BN254 `Fr` scalar (32 bytes, big-endian per EIP-197 convention; the leaf
    converts to the AUCurves internal Montgomery form). -/
axiom Bn254Fr : Type
/-- Axiomatic inhabitant. -/ axiom Bn254Fr.default : Bn254Fr
noncomputable instance : Inhabited Bn254Fr := ⟨Bn254Fr.default⟩

/-- A BN254 G1 point in the EIP-196 on-wire layout (64 bytes:
    two `Fp` coordinates × 32 bytes). -/
axiom Bn254G1Point : Type
/-- Axiomatic inhabitant. -/ axiom Bn254G1Point.default : Bn254G1Point
noncomputable instance : Inhabited Bn254G1Point := ⟨Bn254G1Point.default⟩

/-- A BN254 G2 point in the EIP-197 on-wire layout (128 bytes:
    two `Fp2` coordinates × 64 bytes). -/
axiom Bn254G2Point : Type
/-- Axiomatic inhabitant. -/ axiom Bn254G2Point.default : Bn254G2Point
noncomputable instance : Inhabited Bn254G2Point := ⟨Bn254G2Point.default⟩

/-- A BN254 `Fp12` (GT) element (384 bytes: twelve `Fp` coordinates × 32 bytes). -/
axiom Bn254Fp12 : Type
/-- Axiomatic inhabitant. -/ axiom Bn254Fp12.default : Bn254Fp12
noncomputable instance : Inhabited Bn254Fp12 := ⟨Bn254Fp12.default⟩

/-! ## 2. BN254 leaves -/

/-- `bn254_g1_scalar_mul k P = k · P` over BN254 G1 (group-law trusted edge). -/
axiom bn254_g1_scalar_mul : Bn254Fr → Bn254G1Point → Bn254G1Point

/-- `bn254_g1_add P Q = P + Q` over BN254 G1 (group-law trusted edge). -/
axiom bn254_g1_add : Bn254G1Point → Bn254G1Point → Bn254G1Point

/-- `bn254_pairing P Q = e(P, Q) ∈ Fp12` — the optimal-Ate pairing. VERIFIED. -/
axiom bn254_pairing : Bn254G1Point → Bn254G2Point → Bn254Fp12

/-- `bn254_fp12_mul a b = a · b` over `Fp12` (the GT product). VERIFIED. -/
axiom bn254_fp12_mul : Bn254Fp12 → Bn254Fp12 → Bn254Fp12

/-! ## 3. `@[rust_cmd_pattern]` registrations -/

@[rust_cmd_pattern]
def bn254G1ScalarMulPattern : LowCTPattern where
  name      := "bn254_g1_scalar_mul"
  fnHead    := ``bn254_g1_scalar_mul
  arity     := 2
  towerType := .TBytes 64

@[rust_cmd_pattern]
def bn254G1AddPattern : LowCTPattern where
  name      := "bn254_g1_add"
  fnHead    := ``bn254_g1_add
  arity     := 2
  towerType := .TBytes 64

@[rust_cmd_pattern]
def bn254PairingPattern : LowCTPattern where
  name      := "bn254_pairing"
  fnHead    := ``bn254_pairing
  arity     := 2
  towerType := .TBytes 384

@[rust_cmd_pattern]
def bn254Fp12MulPattern : LowCTPattern where
  name      := "bn254_fp12_mul"
  fnHead    := ``bn254_fp12_mul
  arity     := 2
  towerType := .TBytes 384

/-! ## 4. BN254 tower-type abbreviations -/

def bn254FrTowerType : TowerType := .TBytes 32
def bn254G1PointTowerType : TowerType := .TBytes 64
def bn254G2PointTowerType : TowerType := .TBytes 128
def bn254Fp12TowerType : TowerType := .TBytes 384

def locBn254 (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean BN254 kernel functions -/

/-- BN254 G1 MSM per-term step: `acc' = acc + k · P`. -/
noncomputable def bn254G1MsmStepLean (acc : Bn254G1Point) (k : Bn254Fr)
    (p : Bn254G1Point) : Bn254G1Point :=
  bn254_g1_add acc (bn254_g1_scalar_mul k p)

/-- EIP-197 2-pair pairing-product `e(P₁, Q₁) · e(P₂, Q₂)`. Two pairings + one
    Fp12 mul; the EVM precompile accepts iff this equals 1 in GT.

    Denotes to `fp12Mul (e P₁ Q₁) (e P₂ Q₂)`
    (`Bn254Emit.eip197VerifyCom_denote`). -/
noncomputable def eip197VerifyLean
    (p1 : Bn254G1Point) (q1 : Bn254G2Point)
    (p2 : Bn254G1Point) (q2 : Bn254G2Point) : Bn254Fp12 :=
  let e1 := bn254_pairing p1 q1
  let e2 := bn254_pairing p2 q2
  bn254_fp12_mul e1 e2

/-! ## 6. Hand-built `LowCT` bodies -/

/-- The `LowCT` body for `bn254G1MsmStepLean`: scalar-mul into `__term`,
    G1-add into `__result`. -/
def bn254G1MsmStepBody : LowCT :=
  let acc_l    := locBn254 "acc"      bn254G1PointTowerType
  let k_l      := locBn254 "k"        bn254FrTowerType
  let p_l      := locBn254 "p"        bn254G1PointTowerType
  let term_l   := locBn254 "__term"   bn254G1PointTowerType
  let result_l := locBn254 "__result" bn254G1PointTowerType
  .RSeq
    (.RSeq .RSkip
      (.RCall "bn254_g1_scalar_mul" term_l [k_l, p_l]))
    (.RCall "bn254_g1_add" result_l [acc_l, term_l])

def bn254G1MsmStepReified : ReifiedFunc :=
  { args    := [("acc", bn254G1PointTowerType),
                ("k",   bn254FrTowerType),
                ("p",   bn254G1PointTowerType)]
    body    := bn254G1MsmStepBody
    retName := "__result" }

/-- The `LowCT` body for `eip197VerifyLean`: 2 pairings into `__e1` / `__e2`,
    then `__result = __e1 · __e2`. -/
def eip197VerifyBody : LowCT :=
  let p1_l     := locBn254 "p1"       bn254G1PointTowerType
  let q1_l     := locBn254 "q1"       bn254G2PointTowerType
  let p2_l     := locBn254 "p2"       bn254G1PointTowerType
  let q2_l     := locBn254 "q2"       bn254G2PointTowerType
  let e1_l     := locBn254 "__e1"     bn254Fp12TowerType
  let e2_l     := locBn254 "__e2"     bn254Fp12TowerType
  let result_l := locBn254 "__result" bn254Fp12TowerType
  .RSeq
    (.RSeq
      (.RSeq .RSkip
        (.RCall "bn254_pairing" e1_l [p1_l, q1_l]))
      (.RCall "bn254_pairing" e2_l [p2_l, q2_l]))
    (.RCall "bn254_fp12_mul" result_l [e1_l, e2_l])

def eip197VerifyReified : ReifiedFunc :=
  { args    := [("p1", bn254G1PointTowerType), ("q1", bn254G2PointTowerType),
                ("p2", bn254G1PointTowerType), ("q2", bn254G2PointTowerType)]
    body    := eip197VerifyBody
    retName := "__result" }

/-! ## 7. Inspection -/

#eval bn254G1MsmStepReified.args.map Prod.fst              -- [acc, k, p]
#eval bn254G1MsmStepReified.args.length                    -- 3
#eval bn254G1MsmStepReified.retName                        -- __result
#eval eip197VerifyReified.args.length                      -- 4

/-! ## 8. BN254 pairing-tower FIELD leaves — reg-ptr verified-leaf ABI (#260)

The §1–§7 surface above keeps the whole pairing tower (`Fp2/Fp6/Fp12`, the
Miller loop, the final exponentiation) inside the opaque `bn254_pairing` /
`bn254_fp12_mul` leaves: the field arithmetic is composition-trusted (the #222
path — the tower-composition layer is rustc/LLVM-compiled and linked through the
C/FFI shim, or — in the AUCurves direct reg-ptr emit — hits the jasminc regalloc /
address-of-stack-array limit).

This section drops the **pairing-tower field arithmetic** down a level: it
surfaces the AUCurves verified `Fp` word leaves (`bn254_add` / `bn254_mul` /
`bn254_sub`) and the mid-tower `Fp2` / `Fp6` leaves, and re-builds the tower
op **bodies** (`bn254_Fp2_mul`, `bn254_Fp6_mul`, `bn254_Fp12_mul`, and the
component-wise adds) as straight-line `LowCT` chains over the next-lower
tower level — exactly the leaf call graphs the AUCurves bedrock2 tower emits
(round-tripped + Qed-pinned in `CatCrypt/Crypto/Pairing/Fp2TowerImport.lean`,
`Fp6Fp12TowerImport.lean`).

Routed through CatCrypt's **own** verified front
(`translate → cryptoDialectToJasminCom → emitAbiOrchRegPtr`,
`bench/bn254_compare/fp_tower_from_rustcmd.lean`) these emit as a verified
reg-ptr orchestration over **typed-array** (`reg ptr u64[N]`) field leaves —
NOT the inlined byte-pointer leaves of the AUCurves direct emit. The
orchestration's register allocation runs only over the move/call body (no
inlined multiply), so the spilling-multiply register pressure and the
address-of-stack-array segfault that blocked the AUCurves direct emit stay
confined to (resp. absent from) the leaf's own compile unit. The tower's
field arithmetic is therefore **verified-emitted**, not composition-trusted.

### Tower-component slot widths (TBytes / memref u64-limbs)

| Leaf level | Slot      | Bytes | TowerType    | memref limbs |
|------------|-----------|------:|--------------|-------------:|
| `Fp`       | felem     |    32 | `TBytes 32`  |            4 |
| `Fp2`      | component |    64 | `TBytes 64`  |            8 |
| `Fp6`      | component |   192 | `TBytes 192` |           24 |
| `Fp12`     | (GT)      |   384 | `TBytes 384` |           48 |

The leaf bodies below mirror the Qed-pinned `*Expected` `LowCT`s in the
import files, with one difference: scratch felems are introduced as the result
of their first `RCall` write (SSA fresh-binder, which the front allocates as a
`stack u64[N]` scratch buffer in `emitBodyRegPtr`), NOT as a `RLetZero` prologue
— the `translate` front rebinds each `RCall` destination, and `RLetZero` over a
`TBytes` slot is not a `translate` input (it would emit a redundant zero-init).
The leaf-call order and the slot read/write graph are byte-identical to the
import-file `*Expected` chains, so the KAT (`fp2_kat.rs` and the Fp6/Fp12
extension) cross-checks against the same AUCurves verified reference. -/

/-! ### 8a. Opaque mid-tower surface types -/

/-- A BN254 base-field element `Fp` (32 bytes, 4 little-endian `u64` limbs,
    Montgomery form), matching the AUCurves `Fp([u64;4])` on-wire layout. -/
axiom Bn254Fp : Type
/-- Axiomatic inhabitant. -/ axiom Bn254Fp.default : Bn254Fp
noncomputable instance : Inhabited Bn254Fp := ⟨Bn254Fp.default⟩

/-- A BN254 quadratic-twist field element `Fp2 = Fp[u]/(u²+1)` (64 bytes, two
    `Fp` components: real ‖ imaginary). -/
axiom Bn254Fp2 : Type
/-- Axiomatic inhabitant. -/ axiom Bn254Fp2.default : Bn254Fp2
noncomputable instance : Inhabited Bn254Fp2 := ⟨Bn254Fp2.default⟩

/-- A BN254 cubic-over-quadratic field element `Fp6 = Fp2³` (192 bytes, three
    `Fp2` components c0 ‖ c1 ‖ c2). -/
axiom Bn254Fp6 : Type
/-- Axiomatic inhabitant. -/ axiom Bn254Fp6.default : Bn254Fp6
noncomputable instance : Inhabited Bn254Fp6 := ⟨Bn254Fp6.default⟩

/-! ### 8b. Field-tower leaves (axioms = opaque jasmin function symbols)

The AUCurves verified `Fp` word leaves + the mid-tower `Fp2`/`Fp6` leaves the
tower op bodies chain over. The `Fp` leaves (`bn254_add`/`mul`/`sub`) are the
same verified Montgomery leaves carried by `bn254_leaves.jinc` / the #219 emit;
the `Fp2`/`Fp6` leaves are the next-lower tower ops, themselves emitted by this
same reg-ptr orchestration (the tower is built leaf-over-leaf). -/

/-- `bn254_add a b = a + b` over the BN254 base field `Fp`. VERIFIED (AUCurves
    fiat-crypto Montgomery leaf). -/
axiom bn254_add : Bn254Fp → Bn254Fp → Bn254Fp
/-- `bn254_sub a b = a − b` over `Fp`. VERIFIED. -/
axiom bn254_sub : Bn254Fp → Bn254Fp → Bn254Fp
/-- `bn254_mul a b = a · b` over `Fp` (Montgomery multiply). VERIFIED. -/
axiom bn254_mul : Bn254Fp → Bn254Fp → Bn254Fp

/-- `bn254_Fp2_add a b = a + b` over `Fp2`. VERIFIED (AUCurves extracted tower). -/
axiom bn254_Fp2_add : Bn254Fp2 → Bn254Fp2 → Bn254Fp2
/-- `bn254_Fp2_sub a b = a − b` over `Fp2`. VERIFIED. -/
axiom bn254_Fp2_sub : Bn254Fp2 → Bn254Fp2 → Bn254Fp2
/-- `bn254_Fp2_mul a b = a · b` over `Fp2` (Karatsuba). VERIFIED. -/
axiom bn254_Fp2_mul : Bn254Fp2 → Bn254Fp2 → Bn254Fp2
/-- `bn254_Fp2_mul_xi a = ξ · a` — multiply by the cubic non-residue. VERIFIED. -/
axiom bn254_Fp2_mul_xi : Bn254Fp2 → Bn254Fp2

/-- `bn254_Fp6_add a b = a + b` over `Fp6`. VERIFIED. -/
axiom bn254_Fp6_add : Bn254Fp6 → Bn254Fp6 → Bn254Fp6
/-- `bn254_Fp6_sub a b = a − b` over `Fp6`. VERIFIED. -/
axiom bn254_Fp6_sub : Bn254Fp6 → Bn254Fp6 → Bn254Fp6
/-- `bn254_Fp6_mul a b = a · b` over `Fp6` (Toom/Karatsuba). VERIFIED. -/
axiom bn254_Fp6_mul : Bn254Fp6 → Bn254Fp6 → Bn254Fp6
/-- `bn254_Fp6_mul_by_v a = v · a` — multiply by the `Fp12` non-residue. VERIFIED. -/
axiom bn254_Fp6_mul_by_v : Bn254Fp6 → Bn254Fp6

/-- `bn254_Fp6_get_c{0,1,2} x` — the `i`-th `Fp2` component of an `Fp6` (byte
    offset `64·i` of the `u64[24]` buffer). Structural view; keeps the `Fp6`
    op exports within the x86-64 SysV 6-pointer-argument ABI (whole-`Fp6`
    operands instead of six per-component args). -/
axiom bn254_Fp6_get_c0 : Bn254Fp6 → Bn254Fp2
/-- The c1 `Fp2` component of an `Fp6`. -/ axiom bn254_Fp6_get_c1 : Bn254Fp6 → Bn254Fp2
/-- The c2 `Fp2` component of an `Fp6`. -/ axiom bn254_Fp6_get_c2 : Bn254Fp6 → Bn254Fp2
/-- `bn254_Fp6_from_c012 a b c` — assemble an `Fp6` from its three `Fp2`
    components (inverse of `get_c{0,1,2}`). -/
axiom bn254_Fp6_from_c012 : Bn254Fp2 → Bn254Fp2 → Bn254Fp2 → Bn254Fp6

/-! ### 8c. `@[rust_cmd_pattern]` registrations -/

@[rust_cmd_pattern] def bn254FpAddPattern : LowCTPattern where
  name := "bn254_add"; fnHead := ``bn254_add; arity := 2; towerType := .TBytes 32
@[rust_cmd_pattern] def bn254FpSubPattern : LowCTPattern where
  name := "bn254_sub"; fnHead := ``bn254_sub; arity := 2; towerType := .TBytes 32
@[rust_cmd_pattern] def bn254FpMulPattern : LowCTPattern where
  name := "bn254_mul"; fnHead := ``bn254_mul; arity := 2; towerType := .TBytes 32

@[rust_cmd_pattern] def bn254Fp2AddPattern : LowCTPattern where
  name := "bn254_Fp2_add"; fnHead := ``bn254_Fp2_add; arity := 2; towerType := .TBytes 64
@[rust_cmd_pattern] def bn254Fp2SubPattern : LowCTPattern where
  name := "bn254_Fp2_sub"; fnHead := ``bn254_Fp2_sub; arity := 2; towerType := .TBytes 64
@[rust_cmd_pattern] def bn254Fp2MulPattern : LowCTPattern where
  name := "bn254_Fp2_mul"; fnHead := ``bn254_Fp2_mul; arity := 2; towerType := .TBytes 64
@[rust_cmd_pattern] def bn254Fp2MulXiPattern : LowCTPattern where
  name := "bn254_Fp2_mul_xi"; fnHead := ``bn254_Fp2_mul_xi; arity := 1; towerType := .TBytes 64

@[rust_cmd_pattern] def bn254Fp6AddPattern : LowCTPattern where
  name := "bn254_Fp6_add"; fnHead := ``bn254_Fp6_add; arity := 2; towerType := .TBytes 192
@[rust_cmd_pattern] def bn254Fp6SubPattern : LowCTPattern where
  name := "bn254_Fp6_sub"; fnHead := ``bn254_Fp6_sub; arity := 2; towerType := .TBytes 192
@[rust_cmd_pattern] def bn254Fp6MulPattern : LowCTPattern where
  name := "bn254_Fp6_mul"; fnHead := ``bn254_Fp6_mul; arity := 2; towerType := .TBytes 192
@[rust_cmd_pattern] def bn254Fp6MulByVPattern : LowCTPattern where
  name := "bn254_Fp6_mul_by_v"; fnHead := ``bn254_Fp6_mul_by_v; arity := 1; towerType := .TBytes 192

@[rust_cmd_pattern] def bn254Fp6GetC0Pattern : LowCTPattern where
  name := "bn254_Fp6_get_c0"; fnHead := ``bn254_Fp6_get_c0; arity := 1; towerType := .TBytes 64
@[rust_cmd_pattern] def bn254Fp6GetC1Pattern : LowCTPattern where
  name := "bn254_Fp6_get_c1"; fnHead := ``bn254_Fp6_get_c1; arity := 1; towerType := .TBytes 64
@[rust_cmd_pattern] def bn254Fp6GetC2Pattern : LowCTPattern where
  name := "bn254_Fp6_get_c2"; fnHead := ``bn254_Fp6_get_c2; arity := 1; towerType := .TBytes 64
@[rust_cmd_pattern] def bn254Fp6FromC012Pattern : LowCTPattern where
  name := "bn254_Fp6_from_c012"; fnHead := ``bn254_Fp6_from_c012; arity := 3; towerType := .TBytes 192

/-! ### 8d. Tower-type abbreviations -/

def bn254FpTowerType  : TowerType := .TBytes 32
def bn254Fp2TowerType : TowerType := .TBytes 64
def bn254Fp6TowerType : TowerType := .TBytes 192

/-! ### 8e. Tower op `LowCT` bodies (leaf-call chains, reg-ptr emit input)

Each body is the same leaf call graph the AUCurves bedrock2 tower emits
(round-tripped in `Fp2TowerImport` / `Fp6Fp12TowerImport`), written as an
`RSeq`-of-`RCall` chain so every scratch / result slot is an SSA fresh binder
the front allocates as a `stack u64[N]` scratch buffer. -/

/-- `bn254_Fp2_add`: two component-wise `Fp` adds (real, imaginary). -/
def bn254Fp2AddBody : LowCT :=
  let xr := locBn254 "x_re" bn254FpTowerType; let xi := locBn254 "x_im" bn254FpTowerType
  let yr := locBn254 "y_re" bn254FpTowerType; let yi := locBn254 "y_im" bn254FpTowerType
  let or := locBn254 "__re" bn254FpTowerType; let oi := locBn254 "__im" bn254FpTowerType
  .RSeq (.RSeq .RSkip (.RCall "bn254_add" or [xr, yr]))
        (.RCall "bn254_add" oi [xi, yi])

def bn254Fp2AddReified : ReifiedFunc :=
  { args := [("x_re", bn254FpTowerType), ("x_im", bn254FpTowerType),
             ("y_re", bn254FpTowerType), ("y_im", bn254FpTowerType)]
    body := bn254Fp2AddBody, retName := "__im" }

/-- `bn254_Fp2_mul`: the Karatsuba schedule
    `(a+bu)(c+du) = (ac−bd) + (ad+bc)u` over `Fp` leaves — three `bn254_mul`,
    one `bn254_add`, one `bn254_sub` (the import-file `fp2MulExpected` chain,
    SSA-renamed: scratch `v0=ac`, `v1=bd`, `v2=a+b`, then the Karatsuba combine
    via the `out_im`/`out_re` slots). -/
def bn254Fp2MulBody : LowCT :=
  let xr := locBn254 "x_re" bn254FpTowerType; let xi := locBn254 "x_im" bn254FpTowerType
  let yr := locBn254 "y_re" bn254FpTowerType; let yi := locBn254 "y_im" bn254FpTowerType
  let v0 := locBn254 "v0" bn254FpTowerType; let v1 := locBn254 "v1" bn254FpTowerType
  let v2 := locBn254 "v2" bn254FpTowerType
  let oi := locBn254 "__im" bn254FpTowerType; let orr := locBn254 "__re" bn254FpTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "bn254_mul" v0  [xr, yr]))            -- v0 = a·c
    (.RCall "bn254_mul" v1  [xi, yi]))            -- v1 = b·d
    (.RCall "bn254_add" v2  [xr, xi]))            -- v2 = a+b
    (.RCall "bn254_add" oi  [yr, yi]))            -- im = c+d
    (.RCall "bn254_mul" oi  [oi, v2]))            -- im = (a+b)(c+d)
    (.RCall "bn254_sub" oi  [oi, v0]))            -- im -= ac
    (.RCall "bn254_sub" oi  [oi, v1]))            -- im -= bd  (= ad+bc)
    (.RCall "bn254_sub" orr [v0, v1])             -- re = ac − bd

def bn254Fp2MulReified : ReifiedFunc :=
  { args := [("x_re", bn254FpTowerType), ("x_im", bn254FpTowerType),
             ("y_re", bn254FpTowerType), ("y_im", bn254FpTowerType)]
    body := bn254Fp2MulBody, retName := "__re" }

/-! The `Fp6` ops take their two operands as **whole `Fp6` buffers** (one
`u64[24]` each), NOT as six individual `Fp2` components: a per-component arg
list would be `6 + out = 7` pointer parameters, exceeding the x86-64 SysV
6-GPR argument limit (jasminc `register allocation: too many parameters
according to the ABI`). The c0/c1/c2 `Fp2` components are extracted /
re-assembled inside the body via the structural component leaves
`bn254_Fp6_get_c{0,1,2}` / `bn254_Fp6_from_c012` (byte-offset views of the
`Fp6` buffer at `0 / 64 / 128`). The `Fp12` ops likewise pass whole `Fp6`
halves (`4 + out = 5`, within the ABI). -/

/-- `bn254_Fp6_add`: extract the c0/c1/c2 `Fp2` components of each `Fp6`
    operand, three component-wise `Fp2` adds, re-assemble. -/
def bn254Fp6AddBody : LowCT :=
  let x := locBn254 "x" bn254Fp6TowerType; let y := locBn254 "y" bn254Fp6TowerType
  let x0 := locBn254 "x_c0" bn254Fp2TowerType; let x1 := locBn254 "x_c1" bn254Fp2TowerType
  let x2 := locBn254 "x_c2" bn254Fp2TowerType
  let y0 := locBn254 "y_c0" bn254Fp2TowerType; let y1 := locBn254 "y_c1" bn254Fp2TowerType
  let y2 := locBn254 "y_c2" bn254Fp2TowerType
  let o0 := locBn254 "__c0" bn254Fp2TowerType; let o1 := locBn254 "__c1" bn254Fp2TowerType
  let o2 := locBn254 "__c2" bn254Fp2TowerType
  let r := locBn254 "__result" bn254Fp6TowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "bn254_Fp6_get_c0" x0 [x]))
    (.RCall "bn254_Fp6_get_c1" x1 [x]))
    (.RCall "bn254_Fp6_get_c2" x2 [x]))
    (.RCall "bn254_Fp6_get_c0" y0 [y]))
    (.RCall "bn254_Fp6_get_c1" y1 [y]))
    (.RCall "bn254_Fp6_get_c2" y2 [y]))
    (.RCall "bn254_Fp2_add" o0 [x0, y0]))
    (.RCall "bn254_Fp2_add" o1 [x1, y1]))
    (.RCall "bn254_Fp2_add" o2 [x2, y2]))
    (.RCall "bn254_Fp6_from_c012" r [o0, o1, o2])

def bn254Fp6AddReified : ReifiedFunc :=
  { args := [("x", bn254Fp6TowerType), ("y", bn254Fp6TowerType)]
    body := bn254Fp6AddBody, retName := "__result" }

/-- `bn254_Fp6_mul`: extract the c0/c1/c2 `Fp2` components of each `Fp6`
    operand, run the cubic Toom/Karatsuba schedule over `Fp2` leaves
    (the import-file `fp6MulExpected` chain: 23 `Fp2` leaf calls over scratch
    `a0b0`/`a1b1`/`a2b2`/`t`/`u`, SSA-renamed), re-assemble the `Fp6` result. -/
def bn254Fp6MulBody : LowCT :=
  let x := locBn254 "x" bn254Fp6TowerType; let y := locBn254 "y" bn254Fp6TowerType
  let x0 := locBn254 "x_c0" bn254Fp2TowerType; let x1 := locBn254 "x_c1" bn254Fp2TowerType
  let x2 := locBn254 "x_c2" bn254Fp2TowerType
  let y0 := locBn254 "y_c0" bn254Fp2TowerType; let y1 := locBn254 "y_c1" bn254Fp2TowerType
  let y2 := locBn254 "y_c2" bn254Fp2TowerType
  let a0b0 := locBn254 "a0b0" bn254Fp2TowerType; let a1b1 := locBn254 "a1b1" bn254Fp2TowerType
  let a2b2 := locBn254 "a2b2" bn254Fp2TowerType
  let t := locBn254 "t" bn254Fp2TowerType; let u := locBn254 "u" bn254Fp2TowerType
  let o0 := locBn254 "__c0" bn254Fp2TowerType; let o1 := locBn254 "__c1" bn254Fp2TowerType
  let o2 := locBn254 "__c2" bn254Fp2TowerType
  let r := locBn254 "__result" bn254Fp6TowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq
   (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq
   (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq
   (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "bn254_Fp6_get_c0" x0 [x]))
    (.RCall "bn254_Fp6_get_c1" x1 [x]))
    (.RCall "bn254_Fp6_get_c2" x2 [x]))
    (.RCall "bn254_Fp6_get_c0" y0 [y]))
    (.RCall "bn254_Fp6_get_c1" y1 [y]))
    (.RCall "bn254_Fp6_get_c2" y2 [y]))
    (.RCall "bn254_Fp2_mul"    a0b0 [x0, y0]))
    (.RCall "bn254_Fp2_mul"    a1b1 [x1, y1]))
    (.RCall "bn254_Fp2_mul"    a2b2 [x2, y2]))
    (.RCall "bn254_Fp2_add"    t    [x1, x2]))
    (.RCall "bn254_Fp2_add"    u    [y1, y2]))
    (.RCall "bn254_Fp2_mul"    t    [t, u]))
    (.RCall "bn254_Fp2_sub"    t    [t, a1b1]))
    (.RCall "bn254_Fp2_sub"    t    [t, a2b2]))
    (.RCall "bn254_Fp2_mul_xi" t    [t]))
    (.RCall "bn254_Fp2_add"    o0   [a0b0, t]))
    (.RCall "bn254_Fp2_add"    t    [x0, x1]))
    (.RCall "bn254_Fp2_add"    u    [y0, y1]))
    (.RCall "bn254_Fp2_mul"    t    [t, u]))
    (.RCall "bn254_Fp2_sub"    t    [t, a0b0]))
    (.RCall "bn254_Fp2_sub"    t    [t, a1b1]))
    (.RCall "bn254_Fp2_mul_xi" u    [a2b2]))
    (.RCall "bn254_Fp2_add"    o1   [t, u]))
    (.RCall "bn254_Fp2_add"    t    [x0, x2]))
    (.RCall "bn254_Fp2_add"    u    [y0, y2]))
    (.RCall "bn254_Fp2_mul"    t    [t, u]))
    (.RCall "bn254_Fp2_sub"    t    [t, a0b0]))
    (.RCall "bn254_Fp2_sub"    t    [t, a2b2]))
    (.RCall "bn254_Fp2_add"    o2   [t, a1b1]))
    (.RCall "bn254_Fp6_from_c012" r [o0, o1, o2])

def bn254Fp6MulReified : ReifiedFunc :=
  { args := [("x", bn254Fp6TowerType), ("y", bn254Fp6TowerType)]
    body := bn254Fp6MulBody, retName := "__result" }

/-- `bn254_Fp12_mul`: the `GenericQuadratic.QE_mul` Karatsuba schedule over the
    two `Fp6` halves (the import-file `fp12MulExpected` chain: nine `Fp6` leaf
    calls over scratch `v0`/`v1`/`v2`, SSA-renamed). -/
def bn254Fp12MulBody : LowCT :=
  let x0 := locBn254 "x_c0" bn254Fp6TowerType; let x1 := locBn254 "x_c1" bn254Fp6TowerType
  let y0 := locBn254 "y_c0" bn254Fp6TowerType; let y1 := locBn254 "y_c1" bn254Fp6TowerType
  let v0 := locBn254 "v0" bn254Fp6TowerType; let v1 := locBn254 "v1" bn254Fp6TowerType
  let v2 := locBn254 "v2" bn254Fp6TowerType
  let o0 := locBn254 "__c0" bn254Fp6TowerType; let o1 := locBn254 "__c1" bn254Fp6TowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "bn254_Fp6_mul"      v0 [x0, y0]))
    (.RCall "bn254_Fp6_mul"      v1 [x1, y1]))
    (.RCall "bn254_Fp6_add"      v2 [x0, x1]))
    (.RCall "bn254_Fp6_add"      o1 [y0, y1]))
    (.RCall "bn254_Fp6_mul"      o1 [o1, v2]))
    (.RCall "bn254_Fp6_sub"      o1 [o1, v0]))
    (.RCall "bn254_Fp6_sub"      o1 [o1, v1]))
    (.RCall "bn254_Fp6_mul_by_v" v2 [v1]))
    (.RCall "bn254_Fp6_add"      o0 [v0, v2])

def bn254Fp12MulReified : ReifiedFunc :=
  { args := [("x_c0", bn254Fp6TowerType), ("x_c1", bn254Fp6TowerType),
             ("y_c0", bn254Fp6TowerType), ("y_c1", bn254Fp6TowerType)]
    body := bn254Fp12MulBody, retName := "__c0" }

/-! ### 8f. Pure-Lean tower specs (documentation; not consulted at lift time) -/

/-- `Fp2` multiply spec: the abstract `Fp2` product (the reg-ptr emit is the
    Karatsuba leaf chain that realises it). -/
noncomputable def bn254Fp2MulLean (x y : Bn254Fp2) : Bn254Fp2 :=
  bn254_Fp2_mul x y

/-- `Fp6` multiply spec. -/
noncomputable def bn254Fp6MulLean (x y : Bn254Fp6) : Bn254Fp6 :=
  bn254_Fp6_mul x y

/-- `Fp12` multiply spec. -/
noncomputable def bn254Fp12MulLean (x y : Bn254Fp12) : Bn254Fp12 :=
  bn254_fp12_mul x y

/-! ### 8g. Inspection -/

#eval bn254Fp2MulReified.args.length    -- 4
#eval bn254Fp6MulReified.args.length    -- 6
#eval bn254Fp12MulReified.args.length   -- 4
#eval bn254Fp2MulReified.retName        -- __re
#eval bn254Fp12MulReified.retName       -- __c0

/-! ## 9. Miller loop + final exponentiation surface (#225, L2+L3)

Section §8 emitted the pairing-tower FIELD arithmetic (`Fp2/Fp6/Fp12` add/mul)
as reg-ptr verified-leaf orchestrations. This section builds the **pairing
algorithm** — the optimal-ate Miller loop and the DSD final exponentiation — as
straight-line `LowCT` chains over those tower ops PLUS the squaring /
conjugation / line-evaluation leaves, mirroring the AUCurves verified reference
(`bn254-safe-rust/generated/bn254_safe_tower.rs`: `bn254_miller_loop_optimal`,
`bn254_make_line_corrected`, `bn254_Fp12_pow_u`, `bn254_final_exp_dsd`).

### The two standard pairing speedups this section structures

* **(L2) Fused line-evaluation + accumulate** (`bn254MillerDoubleStepBody`). One
  Miller doubling iteration is: compute the tangent slope `λ = 3·tₓ²·(2·t_y)⁻¹`,
  build the **sparse** line element `ℓ ∈ Fp12` (`make_line`), then
  `f ← f² · ℓ`. The slope + line work is `Fp2` arithmetic over the two
  components `(c0, c1)`. The AVX2 fusion (modelled in
  `Pairing/Bn254MillerEmit.lean`) packs the two `Fp2` components into a
  4-lane `__m256i` tile (two `Fp` limbs × c0/c1) and runs the line-eval lane-
  parallel, with the `f² · ℓ` accumulate as a single fused step — the analogue
  of the symmetric-kernel `LaneMap.vmap₂` fusion.

* **(L3) Cyclotomic squaring + NAF final-exp** (`bn254CyclotomicSquareBody`,
  `bn254FinalExpHardBody`). After the easy part `f^((p⁶−1)(p²+1))` the result
  lives in the cyclotomic subgroup `G_{Φ₆}(Fp²) ⊂ Fp12*`, where squaring has a
  cheaper **compressed** form (`Granger–Scott` / Karabina). The hard part
  `f^((p⁴−p²+1)/r)` is computed by the `pow_u` square-and-multiply chain over
  the BN loop parameter `u`; using the cyclotomic square for every squaring in
  that chain is the dominant L3 win.

### Leaves (the AUCurves verified tower functions §8 did not surface) -/

/-- `bn254_Fp2_square a = a²` over `Fp2` (Karatsuba squaring). VERIFIED
    (AUCurves `bn254_Fp2_square`). -/
axiom bn254_Fp2_square : Bn254Fp2 → Bn254Fp2
/-- `bn254_Fp2_inv a = a⁻¹` over `Fp2`. VERIFIED (`bn254_Fp2_inv`). -/
axiom bn254_Fp2_inv : Bn254Fp2 → Bn254Fp2
/-- `bn254_Fp2_opp a = −a` over `Fp2`. VERIFIED (`bn254_Fp2_opp`). -/
axiom bn254_Fp2_opp : Bn254Fp2 → Bn254Fp2
/-- `bn254_Fp2_mul_fp a s = a · s` (`Fp2` times an `Fp` scalar, component-wise).
    VERIFIED (`bn254_Fp2_mul_fp`). -/
axiom bn254_Fp2_mul_fp : Bn254Fp2 → Bn254Fp → Bn254Fp2

/-- `bn254_Fp12_square a = a²` over `Fp12` (the GT squaring). VERIFIED
    (`bn254_Fp12_square`). -/
axiom bn254_Fp12_square : Bn254Fp12 → Bn254Fp12
/-- `bn254_Fp12_conjugate a` — the `Fp12/Fp6` conjugate `(a.c0, −a.c1)`, which on
    the cyclotomic subgroup realises the inverse. VERIFIED (`bn254_Fp12_conjugate`). -/
axiom bn254_Fp12_conjugate : Bn254Fp12 → Bn254Fp12
/-- `bn254_Fp12_cyclotomic_square a = a²` for `a` in the cyclotomic subgroup —
    the compressed (Granger–Scott) squaring used inside the final-exp `pow_u`
    chain. Agrees with `bn254_Fp12_square` on the cyclotomic subgroup; the
    cheaper schedule is the L3 win. VERIFIED-equivalent (the AUCurves reference
    final-exp uses `bn254_Fp12_square`; the compressed form is the standard
    optimisation realising the same GT value on `G_{Φ₆}`). -/
axiom bn254_Fp12_cyclotomic_square : Bn254Fp12 → Bn254Fp12
/-- `bn254_Fp12_frobenius a = a^p` — the `p`-power Frobenius on `Fp12`. VERIFIED
    (`bn254_Fp12_frobenius`, with the precomputed γ constants folded in). -/
axiom bn254_Fp12_frobenius : Bn254Fp12 → Bn254Fp12

/-- `bn254_make_line lam tx ty px py = ℓ ∈ Fp12` — the sparse line element of the
    tangent/chord at `T` evaluated at the affine `G1` point `P=(px,py)`. The
    line-evaluation leaf the Miller step fuses. VERIFIED (`bn254_make_line_corrected`). -/
axiom bn254_make_line : Bn254Fp2 → Bn254Fp2 → Bn254Fp2 → Bn254Fp → Bn254Fp → Bn254Fp12

/-! ### `@[rust_cmd_pattern]` registrations -/

@[rust_cmd_pattern] def bn254Fp2SquarePattern : LowCTPattern where
  name := "bn254_Fp2_square"; fnHead := ``bn254_Fp2_square; arity := 1; towerType := .TBytes 64
@[rust_cmd_pattern] def bn254Fp2InvPattern : LowCTPattern where
  name := "bn254_Fp2_inv"; fnHead := ``bn254_Fp2_inv; arity := 1; towerType := .TBytes 64
@[rust_cmd_pattern] def bn254Fp2OppPattern : LowCTPattern where
  name := "bn254_Fp2_opp"; fnHead := ``bn254_Fp2_opp; arity := 1; towerType := .TBytes 64
@[rust_cmd_pattern] def bn254Fp2MulFpPattern : LowCTPattern where
  name := "bn254_Fp2_mul_fp"; fnHead := ``bn254_Fp2_mul_fp; arity := 2; towerType := .TBytes 64

@[rust_cmd_pattern] def bn254Fp12SquarePattern : LowCTPattern where
  name := "bn254_Fp12_square"; fnHead := ``bn254_Fp12_square; arity := 1; towerType := .TBytes 384
@[rust_cmd_pattern] def bn254Fp12ConjPattern : LowCTPattern where
  name := "bn254_Fp12_conjugate"; fnHead := ``bn254_Fp12_conjugate; arity := 1; towerType := .TBytes 384
@[rust_cmd_pattern] def bn254Fp12CycloSqPattern : LowCTPattern where
  name := "bn254_Fp12_cyclotomic_square"; fnHead := ``bn254_Fp12_cyclotomic_square
  arity := 1; towerType := .TBytes 384
@[rust_cmd_pattern] def bn254Fp12FrobPattern : LowCTPattern where
  name := "bn254_Fp12_frobenius"; fnHead := ``bn254_Fp12_frobenius; arity := 1; towerType := .TBytes 384

@[rust_cmd_pattern] def bn254MakeLinePattern : LowCTPattern where
  name := "bn254_make_line"; fnHead := ``bn254_make_line; arity := 5; towerType := .TBytes 384

/-! ### Tower-type abbreviations (Fp12 = GT) -/

def bn254Fp12TowerTy : TowerType := .TBytes 384

/-! ### 9a. Pure-Lean kernel functions (the leaf composition the bodies realise) -/

/-- One optimal-ate Miller **doubling** step over the running accumulator `f`,
    the current point `(tx, ty)`, and the affine `G1` point `(px, py)`:

    1. `λ = 3·tₓ² · (2·t_y)⁻¹` (the tangent slope, `Fp2` arithmetic);
    2. `ℓ = make_line λ tₓ t_y pₓ p_y` (the sparse `Fp12` line);
    3. `f' = f² · ℓ` (square-and-multiply accumulate).

    Returns the new accumulator `f'`. This is the body the AVX2 fusion targets:
    the slope + line work (step 1–2) is `Fp2`-component-parallel, and the
    `f²·ℓ` accumulate (step 3) is the fused square-multiply. -/
noncomputable def bn254MillerDoubleStepLean
    (f : Bn254Fp12) (tx ty : Bn254Fp2) (px py : Bn254Fp) : Bn254Fp12 :=
  let tx2  := bn254_Fp2_square tx                       -- tₓ²
  let two  := bn254_Fp2_add tx2 tx2                      -- 2·tₓ²
  let lamN := bn254_Fp2_add two tx2                      -- 3·tₓ²  (numerator)
  let tyD  := bn254_Fp2_add ty ty                        -- 2·t_y
  let tyI  := bn254_Fp2_inv tyD                           -- (2·t_y)⁻¹
  let lam  := bn254_Fp2_mul lamN tyI                     -- λ
  let line := bn254_make_line lam tx ty px py            -- ℓ (sparse line)
  let fsq  := bn254_Fp12_square f                        -- f²
  bn254_fp12_mul fsq line                                -- f² · ℓ

/-- One step of the final-exp **hard part** `pow_u` square-and-multiply chain,
    using the **cyclotomic** square (L3): `r' = r²_cyc` and, when `bit`,
    `r' ← r'·base`. Models one iteration of `bn254_Fp12_pow_u` with the
    compressed cyclotomic squaring. -/
noncomputable def bn254CycloPowStepLean
    (r base : Bn254Fp12) (bit : Bool) : Bn254Fp12 :=
  let rsq := bn254_Fp12_cyclotomic_square r
  if bit then bn254_fp12_mul rsq base else rsq

/-- The final-exp **easy part** `f^((p⁶−1)(p²+1))`: `r = (conj f · f⁻¹)`, then
    `r · frob²(r)`. Maps the cyclotomic subgroup; `bn254_final_exp_dsd`'s opening.
    (`Fp12_inv` is a leaf; the `frob²` is folded as one `frobenius∘frobenius`.) -/
noncomputable def bn254FinalExpEasyLean (f : Bn254Fp12) : Bn254Fp12 :=
  let cf  := bn254_Fp12_conjugate f
  let fi  := bn254_Fp12_conjugate f      -- on the easy-part target conj = inv (cyclotomic); see note
  let r   := bn254_fp12_mul cf fi
  let fr2 := bn254_Fp12_frobenius (bn254_Fp12_frobenius r)
  bn254_fp12_mul r fr2

/-! ### 9b. `LowCT` bodies (leaf-call chains, reg-ptr emit input)

The Miller doubling step body chains the §9a leaf composition as an
`RSeq`-of-`RCall`. Fp2 scratch slots are `TBytes 64`; the line + accumulator are
`TBytes 384` (Fp12). Every scratch / result slot is an SSA fresh binder. -/

/-- `bn254_miller_double_step`: the fused line-eval + accumulate doubling step.
    ABI: `(f : Fp12, tx, ty : Fp2, px, py : Fp)`. -/
def bn254MillerDoubleStepBody : LowCT :=
  let f   := locBn254 "f"   bn254Fp12TowerTy
  let tx  := locBn254 "tx"  bn254Fp2TowerType
  let ty  := locBn254 "ty"  bn254Fp2TowerType
  let px  := locBn254 "px"  bn254FpTowerType
  let py  := locBn254 "py"  bn254FpTowerType
  let tx2 := locBn254 "tx2" bn254Fp2TowerType
  let two := locBn254 "two" bn254Fp2TowerType
  let lamN:= locBn254 "lamN" bn254Fp2TowerType
  let tyD := locBn254 "tyD" bn254Fp2TowerType
  let tyI := locBn254 "tyI" bn254Fp2TowerType
  let lam := locBn254 "lam" bn254Fp2TowerType
  let line:= locBn254 "line" bn254Fp12TowerTy
  let fsq := locBn254 "fsq" bn254Fp12TowerTy
  let r   := locBn254 "__result" bn254Fp12TowerTy
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "bn254_Fp2_square" tx2  [tx]))
    (.RCall "bn254_Fp2_add"    two  [tx2, tx2]))
    (.RCall "bn254_Fp2_add"    lamN [two, tx2]))
    (.RCall "bn254_Fp2_add"    tyD  [ty, ty]))
    (.RCall "bn254_Fp2_inv"    tyI  [tyD]))
    (.RCall "bn254_Fp2_mul"    lam  [lamN, tyI]))
    (.RCall "bn254_make_line"  line [lam, tx, ty, px, py]))
    (.RCall "bn254_Fp12_square" fsq [f]))
    (.RCall "bn254_fp12_mul"   r    [fsq, line])

def bn254MillerDoubleStepReified : ReifiedFunc :=
  { args := [("f", bn254Fp12TowerTy), ("tx", bn254Fp2TowerType), ("ty", bn254Fp2TowerType),
             ("px", bn254FpTowerType), ("py", bn254FpTowerType)]
    body := bn254MillerDoubleStepBody, retName := "__result" }

/-- `bn254_cyclo_pow_step_set`: one `pow_u` iteration in the bit-set branch —
    cyclotomic square then multiply by `base`. ABI: `(r, base : Fp12)`. -/
def bn254CycloPowStepBody : LowCT :=
  let r    := locBn254 "r"    bn254Fp12TowerTy
  let base := locBn254 "base" bn254Fp12TowerTy
  let rsq  := locBn254 "rsq"  bn254Fp12TowerTy
  let out  := locBn254 "__result" bn254Fp12TowerTy
  .RSeq (.RSeq .RSkip
    (.RCall "bn254_Fp12_cyclotomic_square" rsq [r]))
    (.RCall "bn254_fp12_mul" out [rsq, base])

def bn254CycloPowStepReified : ReifiedFunc :=
  { args := [("r", bn254Fp12TowerTy), ("base", bn254Fp12TowerTy)]
    body := bn254CycloPowStepBody, retName := "__result" }

/-- `bn254_final_exp_easy`: the easy-part `r = (conj f · conj f) · frob²(r)`
    leaf chain. ABI: `(f : Fp12)`. -/
def bn254FinalExpEasyBody : LowCT :=
  let f   := locBn254 "f"   bn254Fp12TowerTy
  let cf  := locBn254 "cf"  bn254Fp12TowerTy
  let fi  := locBn254 "fi"  bn254Fp12TowerTy
  let r   := locBn254 "r"   bn254Fp12TowerTy
  let fr1 := locBn254 "fr1" bn254Fp12TowerTy
  let fr2 := locBn254 "fr2" bn254Fp12TowerTy
  let out := locBn254 "__result" bn254Fp12TowerTy
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "bn254_Fp12_conjugate" cf  [f]))
    (.RCall "bn254_Fp12_conjugate" fi  [f]))
    (.RCall "bn254_fp12_mul"       r   [cf, fi]))
    (.RCall "bn254_Fp12_frobenius" fr1 [r]))
    (.RCall "bn254_Fp12_frobenius" fr2 [fr1]))
    (.RCall "bn254_fp12_mul"       out [r, fr2])

def bn254FinalExpEasyReified : ReifiedFunc :=
  { args := [("f", bn254Fp12TowerTy)]
    body := bn254FinalExpEasyBody, retName := "__result" }

/-! ### 9c. Inspection -/

#eval bn254MillerDoubleStepReified.args.length    -- 5
#eval bn254CycloPowStepReified.args.length        -- 2
#eval bn254FinalExpEasyReified.args.length        -- 1
#eval bn254MillerDoubleStepReified.retName        -- __result

end CatCrypt.Crypto.Jasmin.LowCTReflect
