/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTToJasmin
public import CatCrypt.Crypto.Jasmin.RustEmit
public import CatCrypt.Crypto.Jasmin.P384Reflect

/-!
# ECDSA-P384 front: the mod-`n` scalar surface, verify and sign as `LowCT`

This module carries the ECDSA over NIST P-384 (FIPS 186-4, secp384r1)
orchestration as two `LowCT` programs that the compiler's Rust backend
(`ppRustFunction`) renders and the owned front (`toJasminCmd`) lowers.

## Wire ABI

| value | tower type |
| --- | --- |
| scalar mod `n` | `.TBytes 48` |
| message digest `e` | `.TBytes 48` |
| projective point `X ‖ Y ‖ Z` | `.TBytes 144` |
| boolean flag | `.TU64` |

`ppRustFunction` emits inputs as `&T` and outputs as `&mut T`, inputs first
and outputs last. Inside a body, `.RCall f dest args` renders as
`f(dest, args…)` with the destination first.

## Hashing is outside the kernel

`e` is the already-computed, already-reduced message digest: an element of
`ZMod n` in 48-byte wire form. Neither body hashes a message, and neither
body derives a nonce — `k` is an input to the signing body.

## Input validation

The verification body tests its inputs before combining the test outcomes with
the equality result: `r` and `s` must each be an integer in `[1, n-1]`, and the
public key `Q` must be a curve point other than the identity. A signature
failing any of these gives `ok = 0`, so `r = 0`, `s = 0`, a component at or
above `n`, and an identity or off-curve public key are all rejected. The tests
are leaf calls combined by a bitwise `and`, and the arithmetic chain runs
unconditionally, so the body has no branch on an input.

The signing body reports the same range condition on the `r` and `s` it
produces through its `ok` output.

## The generator is fixed in a leaf

The two multiples of the generator — `k·G` in signing and `u₁·G` in
verification — go through `p384_scalar_mul_base`, which takes the scalar alone.
`u₂·Q` uses the variable-base `p384_scalar_mul`.

## The leaves are opaque

Every arithmetic step is a leaf call. The Rust shim implements the
scalar-field leaves over fiat-crypto's `p384_scalar_64.rs`, and the group-law
leaves `p384_scalar_mul` / `p384_point_add` are supplied by the P-384 group
surface. This module proves the orchestration — the sequence, the destinations
and the leaf names — and no arithmetic property of any leaf.

`.RCall` takes its leaf name as a `String`, so the two group-law leaves are
called by name here without a Lean-level declaration in this module.

## Leaf contract for the signing body

`p384EcdsaSignBody` consumes a secret key `d` and a secret nonce `k`. Its
`p384_scalar_mul_base`, `p384_scalar_inv`, `p384_scalar_muln` and
`p384_scalar_addn` leaves therefore carry a constant-time obligation on the
implementation: their execution time and memory-access trace must be
independent of the secret operand. That is a requirement on the shim, not a
property established here; this module claims no constant-time property of the
emitted program.

## No security theorem

Nothing here states an unforgeability, soundness or completeness property of
ECDSA-P384. The theorems below are structural: the Jasmin command count of
each lowered body, and the leaf name of each emitted command.

## Simulation

Both bodies are call-only, so `callFree` is `false` on them and
`rustExecSimulates` does not apply — its `hCF : callFree c = true`
precondition excludes `.RCall`. The applicable statement is
`rustExecSimulates_withCalls`, whose `callFreePlusCall` precondition admits
interleaved `.RCall` leaves. Instantiating it for these bodies requires a
`LeafSpec` and a `TransEnv` in which every leaf named here satisfies
`LeafImplOkNewSid` at every fuel `≥ 2`, together with the `LimbStoreImplOk`
and `CloneImplOk` hypotheses (vacuously available for bodies containing no
`.RLimbStore` and no `.RCloneCall`) and the heap and scalar invariants at the
entry state. Those leaf hypotheses are supplied by the shim's verified leaf
table; this module states none of them.

## References

* FIPS 186-4, Digital Signature Standard, Appendix D.1.2.3 (P-384).
* `CatCrypt.Crypto.Util.ScalarFieldVerified` — `ecdsaU1`, `ecdsaU2`,
  `ecdsaSignS`, the abstract `ZMod n` scalar references these bodies compute.
* `CatCrypt.Crypto.Jasmin.P256Reflect` — the P-256 analogue of this surface.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque P-384 surface types

`P384Scalar` (48 bytes) and `P384Point` (144 bytes, projective `X ‖ Y ‖ Z`),
together with the group-law leaves `p384_scalar_mul`, `p384_scalar_mul_base`
and `p384_point_add` the bodies below call, come from
`CatCrypt.Crypto.Jasmin.P384Reflect`. -/

/-! ## 2. Scalar-field and projection leaves

The Rust shim implements these over fiat-crypto's `p384_scalar_64.rs`. -/

/-- Inverse mod the P-384 group order `n`, constant time. -/
axiom p384_scalar_inv : P384Scalar → P384Scalar

/-- Multiplication mod the P-384 group order `n`. -/
axiom p384_scalar_muln : P384Scalar → P384Scalar → P384Scalar

/-- Addition mod the P-384 group order `n`. -/
axiom p384_scalar_addn : P384Scalar → P384Scalar → P384Scalar

/-- Reduction of a 384-bit value mod the P-384 group order `n`. -/
axiom p384_scalar_reduce : P384Scalar → P384Scalar

/-- The affine `x` coordinate of a projective point, as a 48-byte value. -/
axiom p384_point_affine_x : P384Point → P384Scalar

/-- Equality test on scalars: `1` when the two operands are equal, `0`
    otherwise. -/
axiom p384_scalar_is_eq : P384Scalar → P384Scalar → UInt64

/-! ## 2b. Validity leaves

The three leaves below carry the input conditions of FIPS 186-4 §6.4.2: a
signature component is an integer in `[1, n-1]`, and a public key is a point of
the curve other than the identity. -/

/-- Scalar range test: `1` when the 48-byte operand, read as a little-endian
    integer, satisfies `1 ≤ a < n` for the P-384 group order `n`, and `0`
    otherwise.

    Requirements on the implementation: it compares against `n` rather than
    reducing modulo `n`, so a value at or above `n` yields `0`; it yields `0`
    on zero; and it is constant time, its execution time and memory-access
    trace independent of the operand. -/
axiom p384_scalar_in_range : P384Scalar → UInt64

/-- Point validity test: `1` when the 144-byte projective triple decodes to a
    point satisfying the P-384 curve equation and that point is not the
    identity, and `0` otherwise.

    Requirements on the implementation: it checks the curve equation on the
    decoded coordinates; it yields `0` for the identity, including the `Z = 0`
    encoding of it; and it is constant time, its execution time and
    memory-access trace independent of the operand. -/
axiom p384_point_valid : P384Point → UInt64

/-- Bitwise conjunction of two flags. On operands each `0` or `1` the result is
    `1` exactly when both are `1`.

    Requirements on the implementation: a single `u64` bitwise `and`, with no
    branch on either operand. -/
axiom p384_flag_and : UInt64 → UInt64 → UInt64

/-! ## 3. `@[rust_cmd_pattern]` registrations

`LowCTPattern.towerType` is the destination type and `LowCTPattern.argTypes`
the per-argument types, so the homogeneous and the heterogeneous leaves are
registered alike: the four scalar leaves at `.TBytes 48` and `p384_flag_and`
at `.TU64` carry no `argTypes`, and `p384_point_affine_x` (`144 → 48`),
`p384_scalar_is_eq` (`48 × 48 → u64`), `p384_scalar_in_range` (`48 → u64`)
and `p384_point_valid` (`144 → u64`) each list theirs. -/

/-- Register `p384_scalar_inv` → leaf `p384_scalar_inv`. -/
@[rust_cmd_pattern]
def p384ScalarInvPattern : LowCTPattern where
  name      := "p384_scalar_inv"
  fnHead    := ``p384_scalar_inv
  arity     := 1
  towerType := .TBytes 48

/-- Register `p384_scalar_muln` → leaf `p384_scalar_muln`. -/
@[rust_cmd_pattern]
def p384ScalarMulnPattern : LowCTPattern where
  name      := "p384_scalar_muln"
  fnHead    := ``p384_scalar_muln
  arity     := 2
  towerType := .TBytes 48

/-- Register `p384_scalar_addn` → leaf `p384_scalar_addn`. -/
@[rust_cmd_pattern]
def p384ScalarAddnPattern : LowCTPattern where
  name      := "p384_scalar_addn"
  fnHead    := ``p384_scalar_addn
  arity     := 2
  towerType := .TBytes 48

/-- Register `p384_scalar_reduce` → leaf `p384_scalar_reduce`. -/
@[rust_cmd_pattern]
def p384ScalarReducePattern : LowCTPattern where
  name      := "p384_scalar_reduce"
  fnHead    := ``p384_scalar_reduce
  arity     := 1
  towerType := .TBytes 48

/-- Register `p384_flag_and` → leaf `p384_flag_and`. -/
@[rust_cmd_pattern]
def p384FlagAndPattern : LowCTPattern where
  name      := "p384_flag_and"
  fnHead    := ``p384_flag_and
  arity     := 2
  towerType := .TU64

/-- Register `p384_point_affine_x` → leaf `p384_point_affine_x`: a 144-byte
    projective point to a 48-byte affine `x`. -/
@[rust_cmd_pattern]
def p384PointAffineXPattern : LowCTPattern where
  name      := "p384_point_affine_x"
  fnHead    := ``p384_point_affine_x
  arity     := 1
  towerType := p384ScalarTowerType
  argTypes  := some [p384PointTowerType]

/-- Register `p384_scalar_is_eq` → leaf `p384_scalar_is_eq`: two 48-byte
    scalars to a `u64` flag. -/
@[rust_cmd_pattern]
def p384ScalarIsEqPattern : LowCTPattern where
  name      := "p384_scalar_is_eq"
  fnHead    := ``p384_scalar_is_eq
  arity     := 2
  towerType := .TU64
  argTypes  := some [p384ScalarTowerType, p384ScalarTowerType]

/-- Register `p384_scalar_in_range` → leaf `p384_scalar_in_range`: a 48-byte
    scalar to a `u64` flag. -/
@[rust_cmd_pattern]
def p384ScalarInRangePattern : LowCTPattern where
  name      := "p384_scalar_in_range"
  fnHead    := ``p384_scalar_in_range
  arity     := 1
  towerType := .TU64
  argTypes  := some [p384ScalarTowerType]

/-- Register `p384_point_valid` → leaf `p384_point_valid`: a 144-byte
    projective point to a `u64` flag. -/
@[rust_cmd_pattern]
def p384PointValidPattern : LowCTPattern where
  name      := "p384_point_valid"
  fnHead    := ``p384_point_valid
  arity     := 1
  towerType := .TU64
  argTypes  := some [p384PointTowerType]

/-! ## 4. Slot constructors

`p384ScalarTowerType` (`.TBytes 48`) and `p384PointTowerType` (`.TBytes 144`)
come from `P384Reflect`; a message digest uses the scalar tower type. -/

/-- A scalar slot named `n`. -/
def scP384 (n : String) : Located := { locVar := n, locSrc := p384ScalarTowerType }

/-- A projective-point slot named `n`. -/
def ptP384 (n : String) : Located := { locVar := n, locSrc := p384PointTowerType }

/-- A `u64` flag slot named `n`. -/
def flagP384 (n : String) : Located := { locVar := n, locSrc := .TU64 }

/-- The left-nested `RSeq` chain over a list of commands, starting from
    `RSkip`: the shape a reified straight-line body has. -/
def p384SeqChain (cs : List LowCT) : LowCT := cs.foldl LowCT.RSeq .RSkip

/-- Wrap a body in zero-initialising declarations for the given local slots, so
    the rendered Rust declares each local before its first use. A `.TU64` slot
    uses `RLetU64Zero`, which renders `let mut x : u64 = 0;`; every other tower
    type uses `RLetZero`. -/
def p384WithLocals (ds : List (String × TowerType)) (body : LowCT) : LowCT :=
  ds.foldr
    (fun d acc =>
      match d.2 with
      | .TU64 => .RLetU64Zero d.1 acc
      | t     => .RLetZero d.1 t acc)
    body

/-! ## 5. Pure-Lean kernel specs

The group-law leaves are taken as parameters rather than declared here,
so this module introduces no second declaration of the P-384 group surface. -/

/-- ECDSA-P384 verification, over the opaque leaves: with
    `sinv = s⁻¹`, `u₁ = e·sinv`, `u₂ = r·sinv`, `R = u₁·G + u₂·Q`, the result
    is `1` exactly when all four of `1 ≤ r < n`, `1 ≤ s < n`, `Q` on the curve
    and not the identity, and the affine `x` of `R` reduced mod `n` equal to
    `r`, hold. -/
noncomputable def p384EcdsaVerifyFullLean
    (scalarMul : P384Scalar → P384Point → P384Point)
    (scalarMulBase : P384Scalar → P384Point)
    (pointAdd : P384Point → P384Point → P384Point)
    (e r s : P384Scalar) (Q : P384Point) : UInt64 :=
  let vr   := p384_scalar_in_range r
  let vs   := p384_scalar_in_range s
  let vq   := p384_point_valid Q
  let sinv := p384_scalar_inv s
  let u1   := p384_scalar_muln e sinv
  let u2   := p384_scalar_muln r sinv
  let t1   := scalarMulBase u1
  let t2   := scalarMul u2 Q
  let R    := pointAdd t1 t2
  let x    := p384_point_affine_x R
  let xn   := p384_scalar_reduce x
  let eq   := p384_scalar_is_eq xn r
  p384_flag_and (p384_flag_and (p384_flag_and vr vs) vq) eq

/-- ECDSA-P384 signing, over the opaque leaves: `r` is the affine `x` of
    `k·G` reduced mod `n`, `s = k⁻¹·(e + r·d)`, and `ok` is `1` exactly when
    both `r` and `s` lie in `[1, n-1]`. -/
noncomputable def p384EcdsaSignLean
    (scalarMulBase : P384Scalar → P384Point)
    (e d k : P384Scalar) : P384Scalar × P384Scalar × UInt64 :=
  let R    := scalarMulBase k
  let x    := p384_point_affine_x R
  let r    := p384_scalar_reduce x
  let kinv := p384_scalar_inv k
  let rd   := p384_scalar_muln r d
  let erd  := p384_scalar_addn e rd
  let s    := p384_scalar_muln kinv erd
  (r, s, p384_flag_and (p384_scalar_in_range r) (p384_scalar_in_range s))

/-! ## 6. `LowCT` bodies

Each body is call-only: a left-nested `RSeq` chain of `.RCall` leaves. -/

/-- The `LowCT` body for ECDSA-P384 verification. Inputs `e`, `r`, `s`
    (scalars), `Q` (point); output `ok` (`u64`).

    The three validity leaves run first, the arithmetic chain follows
    unconditionally, and `ok` is the conjunction of the four flags, so the body
    contains no branch on an input. A signature whose `r` or `s` is zero or is
    at or above `n`, and a signature under an identity or off-curve public key,
    give `ok = 0`. -/
def p384EcdsaVerifyFullBody : LowCT :=
  p384SeqChain
    [ .RCall "p384_scalar_in_range"  (flagP384 "vr")  [scP384 "r"],
      .RCall "p384_scalar_in_range"  (flagP384 "vs")  [scP384 "s"],
      .RCall "p384_point_valid"      (flagP384 "vq")  [ptP384 "Q"],
      .RCall "p384_scalar_inv"       (scP384 "sinv")  [scP384 "s"],
      .RCall "p384_scalar_muln"      (scP384 "u1")    [scP384 "e", scP384 "sinv"],
      .RCall "p384_scalar_muln"      (scP384 "u2")    [scP384 "r", scP384 "sinv"],
      .RCall "p384_scalar_mul_base"  (ptP384 "t1")    [scP384 "u1"],
      .RCall "p384_scalar_mul"       (ptP384 "t2")    [scP384 "u2", ptP384 "Q"],
      .RCall "p384_point_add"        (ptP384 "R")     [ptP384 "t1", ptP384 "t2"],
      .RCall "p384_point_affine_x"   (scP384 "x")     [ptP384 "R"],
      .RCall "p384_scalar_reduce"    (scP384 "xn")    [scP384 "x"],
      .RCall "p384_scalar_is_eq"     (flagP384 "eq")  [scP384 "xn", scP384 "r"],
      .RCall "p384_flag_and"         (flagP384 "c1")  [flagP384 "vr", flagP384 "vs"],
      .RCall "p384_flag_and"         (flagP384 "c2")  [flagP384 "c1", flagP384 "vq"],
      .RCall "p384_flag_and"         (flagP384 "ok")  [flagP384 "c2", flagP384 "eq"] ]

/-- The `LowCT` body for ECDSA-P384 signing. Inputs `e` (digest), `d` (secret
    key), `k` (secret nonce); outputs `r`, `s` and `ok` (`u64`).

    `ok` is `1` exactly when both `r` and `s` lie in `[1, n-1]`. The nonce is
    an input, so the body cannot resample it: a caller that reads `ok = 0`
    must draw a fresh `k` and call again, and must not use the `r` and `s` of
    that call. -/
def p384EcdsaSignBody : LowCT :=
  p384SeqChain
    [ .RCall "p384_scalar_mul_base"  (ptP384 "R")    [scP384 "k"],
      .RCall "p384_point_affine_x" (scP384 "x")    [ptP384 "R"],
      .RCall "p384_scalar_reduce"  (scP384 "r")    [scP384 "x"],
      .RCall "p384_scalar_inv"     (scP384 "kinv") [scP384 "k"],
      .RCall "p384_scalar_muln"    (scP384 "rd")   [scP384 "r", scP384 "d"],
      .RCall "p384_scalar_addn"    (scP384 "erd")  [scP384 "e", scP384 "rd"],
      .RCall "p384_scalar_muln"    (scP384 "s")    [scP384 "kinv", scP384 "erd"],
      .RCall "p384_scalar_in_range" (flagP384 "vr") [scP384 "r"],
      .RCall "p384_scalar_in_range" (flagP384 "vs") [scP384 "s"],
      .RCall "p384_flag_and"        (flagP384 "ok") [flagP384 "vr", flagP384 "vs"] ]

/-- `ReifiedFunc` bundle for the verification kernel. -/
def p384EcdsaVerifyFullReified : ReifiedFunc :=
  { args     := [("e", p384ScalarTowerType),
                 ("r", p384ScalarTowerType),
                 ("s", p384ScalarTowerType),
                 ("Q", p384PointTowerType)]
    body     := p384EcdsaVerifyFullBody
    retName  := "ok"
    outNames := ["ok"] }

/-- `ReifiedFunc` bundle for the signing kernel. Three outputs. -/
def p384EcdsaSignReified : ReifiedFunc :=
  { args     := [("e", p384ScalarTowerType),
                 ("d", p384ScalarTowerType),
                 ("k", p384ScalarTowerType)]
    body     := p384EcdsaSignBody
    retName  := "s"
    outNames := ["r", "s", "ok"] }

/-! ## 7. Rust rendering

The rendered bodies wrap the call-only bodies of §6 in `RLetZero`
declarations for their locals, so the emitted function declares each local
before its first use. -/

/-- Input slots of the verification function. -/
def p384EcdsaVerifyFullParams : List Located :=
  [scP384 "e", scP384 "r", scP384 "s", ptP384 "Q"]

/-- Output slots of the verification function. -/
def p384EcdsaVerifyFullResults : List Located := [flagP384 "ok"]

/-- The verification body with its local slots declared. -/
def p384EcdsaVerifyFullRustBody : LowCT :=
  p384WithLocals
    [("vr", .TU64), ("vs", .TU64), ("vq", .TU64),
     ("sinv", p384ScalarTowerType), ("u1", p384ScalarTowerType),
     ("u2", p384ScalarTowerType), ("t1", p384PointTowerType),
     ("t2", p384PointTowerType), ("R", p384PointTowerType),
     ("x", p384ScalarTowerType), ("xn", p384ScalarTowerType),
     ("eq", .TU64), ("c1", .TU64), ("c2", .TU64)]
    p384EcdsaVerifyFullBody

/-- Input slots of the signing function. -/
def p384EcdsaSignParams : List Located :=
  [scP384 "e", scP384 "d", scP384 "k"]

/-- Output slots of the signing function. -/
def p384EcdsaSignResults : List Located :=
  [scP384 "r", scP384 "s", flagP384 "ok"]

/-- The signing body with its local slots declared. -/
def p384EcdsaSignRustBody : LowCT :=
  p384WithLocals
    [("R", p384PointTowerType), ("x", p384ScalarTowerType),
     ("kinv", p384ScalarTowerType), ("rd", p384ScalarTowerType),
     ("erd", p384ScalarTowerType), ("vr", .TU64), ("vs", .TU64)]
    p384EcdsaSignBody

/-- The Rust source of the ECDSA-P384 verification function. -/
def p384EcdsaVerifyFullRust : String :=
  ppRustFunction "p384_ecdsa_verify"
    p384EcdsaVerifyFullParams p384EcdsaVerifyFullResults p384EcdsaVerifyFullRustBody

/-- The Rust source of the ECDSA-P384 signing function. -/
def p384EcdsaSignRust : String :=
  ppRustFunction "p384_ecdsa_sign"
    p384EcdsaSignParams p384EcdsaSignResults p384EcdsaSignRustBody

/-- Write both rendered Rust functions under `bench/p384_ecdsa_rust/gen/`. -/
def emitP384EcdsaRust : IO Unit := do
  IO.FS.createDirAll "bench/p384_ecdsa_rust/gen"
  IO.FS.writeFile
    "bench/p384_ecdsa_rust/gen/p384_ecdsa_verify.rs" p384EcdsaVerifyFullRust
  IO.println "wrote bench/p384_ecdsa_rust/gen/p384_ecdsa_verify.rs"
  IO.FS.writeFile
    "bench/p384_ecdsa_rust/gen/p384_ecdsa_sign.rs" p384EcdsaSignRust
  IO.println "wrote bench/p384_ecdsa_rust/gen/p384_ecdsa_sign.rs"

/-! ## 8. Structural lowering through the owned front -/

/-- The verification body, lowered through the owned front. -/
def p384EcdsaVerifyFullJasmin : Cmd := toJasminCmd p384EcdsaVerifyFullBody

/-- The signing body, lowered through the owned front. -/
def p384EcdsaSignJasmin : Cmd := toJasminCmd p384EcdsaSignBody

/-- The verification body lowers to fifteen Jasmin commands, one per leaf. -/
theorem p384EcdsaVerifyFullJasmin_length : p384EcdsaVerifyFullJasmin.length = 15 := rfl

/-- Every command the front emits for the verification body is a `Ccall` — no
    fall-through to an unhandled construct. -/
theorem p384EcdsaVerifyFullJasmin_all_calls :
    p384EcdsaVerifyFullJasmin.all
      (fun i => match i with | .Ccall .. => true | _ => false) = true := rfl

/-- The leaf name of each command the front emits for the verification body. -/
theorem p384EcdsaVerifyFullJasmin_call_names :
    p384EcdsaVerifyFullJasmin.map
        (fun i => match i with | .Ccall _ _ fn _ => fn.name | _ => "") =
      ["p384_scalar_in_range", "p384_scalar_in_range", "p384_point_valid",
       "p384_scalar_inv", "p384_scalar_muln", "p384_scalar_muln",
       "p384_scalar_mul_base", "p384_scalar_mul", "p384_point_add",
       "p384_point_affine_x", "p384_scalar_reduce", "p384_scalar_is_eq",
       "p384_flag_and", "p384_flag_and", "p384_flag_and"] := rfl

/-- The signing body lowers to ten Jasmin commands, one per leaf. -/
theorem p384EcdsaSignJasmin_length : p384EcdsaSignJasmin.length = 10 := rfl

/-- Every command the front emits for the signing body is a `Ccall`. -/
theorem p384EcdsaSignJasmin_all_calls :
    p384EcdsaSignJasmin.all
      (fun i => match i with | .Ccall .. => true | _ => false) = true := rfl

/-- The leaf name of each command the front emits for the signing body. The
    four scalar-field leaves named here carry the constant-time obligation
    stated in the module header. -/
theorem p384EcdsaSignJasmin_call_names :
    p384EcdsaSignJasmin.map
        (fun i => match i with | .Ccall _ _ fn _ => fn.name | _ => "") =
      ["p384_scalar_mul_base", "p384_point_affine_x", "p384_scalar_reduce",
       "p384_scalar_inv", "p384_scalar_muln", "p384_scalar_addn",
       "p384_scalar_muln", "p384_scalar_in_range", "p384_scalar_in_range",
       "p384_flag_and"] := rfl

/-! ## 9. Argument and result names

The four pins below fix the wire order of each bundle's parameters and
results, which is the order `ppRustFunction` renders into the emitted
signature and the shim crate calls. -/

/-- Parameter order of the verify bundle. -/
example : p384EcdsaVerifyFullReified.args.map Prod.fst = ["e", "r", "s", "Q"] := rfl

/-- Result order of the verify bundle. -/
example : p384EcdsaVerifyFullReified.outNames = ["ok"] := rfl

/-- Parameter order of the signing bundle. -/
example : p384EcdsaSignReified.args.map Prod.fst = ["e", "d", "k"] := rfl

/-- Result order of the signing bundle. -/
example : p384EcdsaSignReified.outNames = ["r", "s", "ok"] := rfl
end CatCrypt.Crypto.Jasmin.LowCTReflect
