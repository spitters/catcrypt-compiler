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
public import CatCrypt.Crypto.Jasmin.P384EcdsaReflect

/-!
# DHKEM(P-384, HKDF-SHA384) front: Encap and Decap as `LowCT`

This module carries the RFC 9180 DHKEM with KEM identifier `0x0011`,
DHKEM(P-384, HKDF-SHA384), as two call-only `LowCT` programs that the
compiler's Rust backend (`ppRustFunction`) renders and the owned front
(`toJasminCmd`) lowers. It follows the ECDSA-P384 front in
`CatCrypt.Crypto.Jasmin.P384EcdsaReflect`, whose slot constructors, validity
leaves and flag conjunction it reuses.

## Scope

The module covers the KEM alone: `Encap(pkR)` and `Decap(enc, skR)` of
RFC 9180 §4.1. HPKE's key schedule, its AEAD and its single-shot APIs are not
here. `GenerateKeyPair` and `DeriveKeyPair` are outside the kernel, as is the
randomness they consume: the encapsulation body takes the ephemeral secret
`skE` as an input, exactly as the ECDSA signing body takes its nonce.

## Wire ABI

| value | tower type |
| --- | --- |
| scalar (`skE`, `skR`) | `.TBytes 48`, the scalar form of `P384Reflect` |
| projective point `X ‖ Y ‖ Z` | `.TBytes 144` |
| SEC1 uncompressed public key, `enc` | `.TBytes 97` |
| DH output, `prk`, shared secret | `.TBytes 48` |
| KEM context `enc ‖ pkRm` | `.TBytes 194` |
| validity flag | `.TU64` |

A secret key is passed in the scalar form of `P384Reflect` (six little-endian
64-bit limbs), which is the input form of `p384_scalar_in_range` and
`p384_scalar_mul`. RFC 9180 §7.1.2 serialises a P-384 private key as a
48-byte big-endian octet string; conversion between the two is the caller's.

These sizes are those of `dhkem_p384` in
`SSProve-lean/CatCrypt/Crypto/HPKE/TestVectors.lean` (`Nsecret = 48`,
`Nenc = 97`, `Npk = 97`, `Nsk = 48`), which RFC 9180 Table 2 fixes.

`ppRustFunction` emits inputs as `&T` and outputs as `&mut T`, inputs first and
outputs last. Inside a body, `.RCall f dest args` renders as `f(dest, args…)`
with the destination first.

## Validation and the `ok` output

RFC 9180 §7.1.4 requires partial public-key validation of every public-key
input for the NIST curves: coordinates below `p`, the point on the curve, the
point not the identity. `p384_sec1_valid` is that test. The DH output is not
the identity whenever the scalar lies in `[1, n-1]` and the point is a valid
non-identity point, because the P-384 group has prime order `n`; the bodies
therefore test the scalar with `p384_scalar_in_range` and the public-key input
with `p384_sec1_valid`, and combine the two flags into `ok`.

Neither body branches on an input: the whole chain runs unconditionally and the
flags are combined by `p384_flag_and` at the end. The shared secret written by a
call that returns `ok = 0` is not a DHKEM output, and the caller must discard it
and treat the call as an RFC 9180 `ValidationError` (on `Decap`) or
`EncapError` (on `Encap`).

## The leaves are opaque

Every step is a leaf call. The two KDF leaves carry HKDF-SHA384, and SHA-384 is
external to this workspace. The module proves the orchestration only — the call
sequence, the destinations and the leaf names — and no arithmetic,
serialisation or KDF property of any leaf.

## No security theorem

Nothing here states an IND-CCA, correctness or constant-time property of the
KEM or of the emitted program. The requirements stated at each leaf are
obligations on the implementation, not properties established here.

## Simulation

Both bodies are call-only, so `callFree` is `false` on them and
`rustExecSimulates` does not apply. The applicable statement is
`rustExecSimulates_withCalls`, whose `callFreePlusCall` precondition admits
interleaved `.RCall` leaves. Instantiating it for these bodies requires a
`LeafSpec` and a `TransEnv` in which every leaf named here satisfies
`LeafImplOkNewSid` at every fuel `≥ 2`, together with the `LimbStoreImplOk`
and `CloneImplOk` hypotheses (vacuously available for bodies containing no
`.RLimbStore` and no `.RCloneCall`) and the heap and scalar invariants at the
entry state. This module states none of them.

## Main results

* `p384DhkemEncapBody`, `p384DhkemDecapBody` — the two call-only bodies.
* `p384DhkemEncapRust`, `p384DhkemDecapRust`, `emitP384DhkemRust` — the
  rendered Rust functions `p384_dhkem_encap` and `p384_dhkem_decap`.
* `p384DhkemEncapJasmin_call_names`, `p384DhkemDecapJasmin_call_names` — the
  ordered leaf names of each lowered body.

## References

* RFC 9180, Hybrid Public Key Encryption: §4 (`LabeledExtract`,
  `LabeledExpand`), §4.1 (DHKEM, `suite_id`, `ExtractAndExpand`), §7.1
  (Table 2), §7.1.1 (serialisation), §7.1.4 (validation).
* SEC 1 v2.0, §2.3.3 and §2.3.4 (uncompressed point encoding).
* `CatCrypt.Crypto.Jasmin.P384EcdsaReflect` — the ECDSA-P384 front.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque byte-string types

A 48-byte octet string (DH output, `prk`, shared secret) uses `P384Scalar` from
`P384Reflect` as its opaque 48-byte carrier, as the ECDSA front does for the
digest and the affine `x`. -/

/-- A 97-byte SEC1 uncompressed P-384 point encoding `0x04 ‖ x ‖ y`, with `x`
    and `y` 48-byte big-endian. Opaque. -/
axiom P384Sec1 : Type
/-- Axiomatic inhabitant. -/ axiom P384Sec1.default : P384Sec1
noncomputable instance : Inhabited P384Sec1 := ⟨P384Sec1.default⟩

/-- A 194-byte DHKEM(P-384) KEM context `enc ‖ pkRm`. Opaque. -/
axiom P384KemContext : Type
/-- Axiomatic inhabitant. -/ axiom P384KemContext.default : P384KemContext
noncomputable instance : Inhabited P384KemContext := ⟨P384KemContext.default⟩

/-- Tower type of a SEC1 uncompressed P-384 point encoding. -/
def p384Sec1TowerType : TowerType := .TBytes 97

/-- Tower type of a DHKEM(P-384) KEM context. -/
def p384KemContextTowerType : TowerType := .TBytes 194

/-! ## 2. Leaves -/

/-- SEC1 decoding: the 97-byte uncompressed encoding `0x04 ‖ x ‖ y` to the
    144-byte projective form of `P384Reflect` of the affine point `(x, y)`.

    Requirements on the implementation: on an input for which
    `p384_sec1_valid` yields `1` it returns that point; on any other input it
    returns some 144-byte value without faulting; and it is constant time, its
    execution time and memory-access trace independent of the operand. -/
axiom p384_sec1_decode : P384Sec1 → P384Point

/-- SEC1 validity test: `1` when the 97-byte operand has prefix byte `0x04`,
    both 48-byte big-endian coordinates are below the P-384 field prime `p`,
    and `(x, y)` satisfies the P-384 curve equation; `0` otherwise. An operand
    passing the test is not the identity, which has no uncompressed encoding.
    This is the partial public-key validation RFC 9180 §7.1.4 requires.

    Requirements on the implementation: it compares the coordinates against
    `p` rather than reducing them; and it is constant time, its execution time
    and memory-access trace independent of the operand. -/
axiom p384_sec1_valid : P384Sec1 → UInt64

/-- SEC1 encoding: a 144-byte projective point to the 97-byte uncompressed
    encoding `0x04 ‖ x ‖ y` of its affine coordinates, each 48-byte big-endian.
    This is `SerializePublicKey` of RFC 9180 §7.1.1 for P-384.

    Requirements on the implementation: it computes the affine coordinates of a
    non-identity point correctly; its output on the identity is unspecified;
    and it is constant time, its execution time and memory-access trace
    independent of the operand, since in `Encap` the operand is `skE · G`. -/
axiom p384_sec1_encode : P384Point → P384Sec1

/-- DH output: the affine `x` coordinate of a 144-byte projective point as a
    48-byte big-endian octet string, which RFC 9180 §7.1 takes as the
    Diffie-Hellman shared secret for P-384 (`Ndh = 48`).

    Requirements on the implementation: it is correct on every non-identity
    point, and it is constant time, its execution time and memory-access trace
    independent of the operand. -/
axiom p384_dh_x_be : P384Point → P384Scalar

/-- KEM context: the 194-byte concatenation `enc ‖ pkRm` of RFC 9180 §4.1, the
    first operand at offsets `0..96` and the second at `97..193`.

    Requirements on the implementation: a byte copy with no branch on either
    operand. -/
axiom p384_kem_context : P384Sec1 → P384Sec1 → P384KemContext

/-- `LabeledExtract("", "eae_prk", dh)` of RFC 9180 §4 and §4.1 for
    DHKEM(P-384, HKDF-SHA384): `HKDF-Extract` over SHA-384 with the empty salt
    applied to
    `labeled_ikm = "HPKE-v1" ‖ suite_id ‖ "eae_prk" ‖ dh`,
    where `suite_id = "KEM" ‖ I2OSP(0x0011, 2)`, i.e. the five bytes
    `4b 45 4d 00 11`. The result is the 48-byte `eae_prk`.

    Requirements on the implementation: SHA-384 per FIPS 180-4 and HMAC per
    RFC 2104, and constant time in `dh`, its execution time and memory-access
    trace independent of the operand. -/
axiom dhkem_p384_extract : P384Scalar → P384Scalar

/-- `LabeledExpand(eae_prk, "shared_secret", kem_context, 48)` of RFC 9180 §4
    and §4.1 for DHKEM(P-384, HKDF-SHA384): `HKDF-Expand` over SHA-384 with
    output length `L = 48` applied to `eae_prk` and
    `labeled_info = I2OSP(48, 2) ‖ "HPKE-v1" ‖ suite_id ‖ "shared_secret" ‖ kem_context`,
    where `suite_id = "KEM" ‖ I2OSP(0x0011, 2)`. The result is the 48-byte
    `shared_secret` (`Nsecret = 48`).

    Requirements on the implementation: SHA-384 per FIPS 180-4 and HMAC per
    RFC 2104, and constant time in `eae_prk`, its execution time and
    memory-access trace independent of that operand. -/
axiom dhkem_p384_expand : P384Scalar → P384KemContext → P384Scalar

/-! ## 3. `@[rust_cmd_pattern]` registrations

Each leaf is heterogeneous in width, so every registration lists its
per-argument tower types. -/

/-- Register `p384_sec1_decode`: 97 bytes to a 144-byte point. -/
@[rust_cmd_pattern]
def p384Sec1DecodePattern : LowCTPattern where
  name      := "p384_sec1_decode"
  fnHead    := ``p384_sec1_decode
  arity     := 1
  towerType := p384PointTowerType
  argTypes  := some [p384Sec1TowerType]

/-- Register `p384_sec1_valid`: 97 bytes to a `u64` flag. -/
@[rust_cmd_pattern]
def p384Sec1ValidPattern : LowCTPattern where
  name      := "p384_sec1_valid"
  fnHead    := ``p384_sec1_valid
  arity     := 1
  towerType := .TU64
  argTypes  := some [p384Sec1TowerType]

/-- Register `p384_sec1_encode`: a 144-byte point to 97 bytes. -/
@[rust_cmd_pattern]
def p384Sec1EncodePattern : LowCTPattern where
  name      := "p384_sec1_encode"
  fnHead    := ``p384_sec1_encode
  arity     := 1
  towerType := p384Sec1TowerType
  argTypes  := some [p384PointTowerType]

/-- Register `p384_dh_x_be`: a 144-byte point to 48 bytes. -/
@[rust_cmd_pattern]
def p384DhXBePattern : LowCTPattern where
  name      := "p384_dh_x_be"
  fnHead    := ``p384_dh_x_be
  arity     := 1
  towerType := p384ScalarTowerType
  argTypes  := some [p384PointTowerType]

/-- Register `p384_kem_context`: two 97-byte strings to 194 bytes. -/
@[rust_cmd_pattern]
def p384KemContextPattern : LowCTPattern where
  name      := "p384_kem_context"
  fnHead    := ``p384_kem_context
  arity     := 2
  towerType := p384KemContextTowerType
  argTypes  := some [p384Sec1TowerType, p384Sec1TowerType]

/-- Register `dhkem_p384_extract`: 48 bytes to 48 bytes. -/
@[rust_cmd_pattern]
def dhkemP384ExtractPattern : LowCTPattern where
  name      := "dhkem_p384_extract"
  fnHead    := ``dhkem_p384_extract
  arity     := 1
  towerType := p384ScalarTowerType
  argTypes  := some [p384ScalarTowerType]

/-- Register `dhkem_p384_expand`: 48 and 194 bytes to 48 bytes. -/
@[rust_cmd_pattern]
def dhkemP384ExpandPattern : LowCTPattern where
  name      := "dhkem_p384_expand"
  fnHead    := ``dhkem_p384_expand
  arity     := 2
  towerType := p384ScalarTowerType
  argTypes  := some [p384ScalarTowerType, p384KemContextTowerType]

/-! ## 4. Slot constructors

48-byte, 144-byte and `u64` slots use `scP384`, `ptP384` and `flagP384` from
`P384EcdsaReflect`. -/

/-- A 97-byte SEC1 slot named `n`. -/
def sec1P384 (n : String) : Located := { locVar := n, locSrc := p384Sec1TowerType }

/-- A 194-byte KEM-context slot named `n`. -/
def kemCtxP384 (n : String) : Located :=
  { locVar := n, locSrc := p384KemContextTowerType }

/-! ## 5. Pure-Lean kernel specifications -/

/-- DHKEM(P-384) `Encap` over the opaque leaves, with the ephemeral secret
    `skE` supplied: the result is `(enc, shared_secret, ok)` with
    `enc = SerializePublicKey(skE·G)`, `dh = x(skE·pkR)` big-endian,
    `shared_secret = ExtractAndExpand(dh, enc ‖ pkR)`, and `ok = 1` exactly
    when `skE ∈ [1, n-1]` and `pkR` passes SEC1 validation. -/
noncomputable def p384DhkemEncapLean
    (skE : P384Scalar) (pkR : P384Sec1) : P384Sec1 × P384Scalar × UInt64 :=
  let vs  := p384_scalar_in_range skE
  let vk  := p384_sec1_valid pkR
  let Q   := p384_sec1_decode pkR
  let E   := p384_scalar_mul_base skE
  let enc := p384_sec1_encode E
  let Z   := p384_scalar_mul skE Q
  let dh  := p384_dh_x_be Z
  let ctx := p384_kem_context enc pkR
  let prk := dhkem_p384_extract dh
  let ss  := dhkem_p384_expand prk ctx
  (enc, ss, p384_flag_and vs vk)

/-- DHKEM(P-384) `Decap` over the opaque leaves: the result is
    `(shared_secret, ok)` with `dh = x(skR·enc)` big-endian,
    `shared_secret = ExtractAndExpand(dh, enc ‖ pkR)`, and `ok = 1` exactly
    when `enc` passes SEC1 validation and `skR ∈ [1, n-1]`. -/
noncomputable def p384DhkemDecapLean
    (enc : P384Sec1) (skR : P384Scalar) (pkR : P384Sec1) : P384Scalar × UInt64 :=
  let ve  := p384_sec1_valid enc
  let vs  := p384_scalar_in_range skR
  let E   := p384_sec1_decode enc
  let Z   := p384_scalar_mul skR E
  let dh  := p384_dh_x_be Z
  let ctx := p384_kem_context enc pkR
  let prk := dhkem_p384_extract dh
  let ss  := dhkem_p384_expand prk ctx
  (ss, p384_flag_and ve vs)

/-! ## 6. `LowCT` bodies

Each body is call-only: a left-nested `RSeq` chain of `.RCall` leaves. -/

/-- The `LowCT` body for DHKEM(P-384) `Encap`. Inputs `skE` (scalar), `pkR`
    (SEC1); outputs `enc` (SEC1), `ss` (48 bytes), `ok` (`u64`).

    The chain runs unconditionally and `ok` is the conjunction of the two
    validity flags, so the body contains no branch on an input. A caller that
    reads `ok = 0` must discard `enc` and `ss`. -/
def p384DhkemEncapBody : LowCT :=
  p384SeqChain
    [ .RCall "p384_scalar_in_range" (flagP384 "vs")   [scP384 "skE"],
      .RCall "p384_sec1_valid"      (flagP384 "vk")   [sec1P384 "pkR"],
      .RCall "p384_sec1_decode"     (ptP384 "Q")      [sec1P384 "pkR"],
      .RCall "p384_scalar_mul_base" (ptP384 "E")      [scP384 "skE"],
      .RCall "p384_sec1_encode"     (sec1P384 "enc")  [ptP384 "E"],
      .RCall "p384_scalar_mul"      (ptP384 "Z")      [scP384 "skE", ptP384 "Q"],
      .RCall "p384_dh_x_be"         (scP384 "dh")     [ptP384 "Z"],
      .RCall "p384_kem_context"     (kemCtxP384 "ctx") [sec1P384 "enc", sec1P384 "pkR"],
      .RCall "dhkem_p384_extract"   (scP384 "prk")    [scP384 "dh"],
      .RCall "dhkem_p384_expand"    (scP384 "ss")     [scP384 "prk", kemCtxP384 "ctx"],
      .RCall "p384_flag_and"        (flagP384 "ok")   [flagP384 "vs", flagP384 "vk"] ]

/-- The `LowCT` body for DHKEM(P-384) `Decap`. Inputs `enc` (SEC1), `skR`
    (scalar), `pkR` (SEC1, the recipient's own public key, which enters the KEM
    context); outputs `ss` (48 bytes), `ok` (`u64`).

    The chain runs unconditionally and `ok` is the conjunction of the two
    validity flags, so the body contains no branch on an input. A caller that
    reads `ok = 0` must discard `ss`. -/
def p384DhkemDecapBody : LowCT :=
  p384SeqChain
    [ .RCall "p384_sec1_valid"      (flagP384 "ve")   [sec1P384 "enc"],
      .RCall "p384_scalar_in_range" (flagP384 "vs")   [scP384 "skR"],
      .RCall "p384_sec1_decode"     (ptP384 "E")      [sec1P384 "enc"],
      .RCall "p384_scalar_mul"      (ptP384 "Z")      [scP384 "skR", ptP384 "E"],
      .RCall "p384_dh_x_be"         (scP384 "dh")     [ptP384 "Z"],
      .RCall "p384_kem_context"     (kemCtxP384 "ctx") [sec1P384 "enc", sec1P384 "pkR"],
      .RCall "dhkem_p384_extract"   (scP384 "prk")    [scP384 "dh"],
      .RCall "dhkem_p384_expand"    (scP384 "ss")     [scP384 "prk", kemCtxP384 "ctx"],
      .RCall "p384_flag_and"        (flagP384 "ok")   [flagP384 "ve", flagP384 "vs"] ]

/-- `ReifiedFunc` bundle for the `Encap` kernel. Three outputs. -/
def p384DhkemEncapReified : ReifiedFunc :=
  { args     := [("skE", p384ScalarTowerType), ("pkR", p384Sec1TowerType)]
    body     := p384DhkemEncapBody
    retName  := "ss"
    outNames := ["enc", "ss", "ok"] }

/-- `ReifiedFunc` bundle for the `Decap` kernel. Two outputs. -/
def p384DhkemDecapReified : ReifiedFunc :=
  { args     := [("enc", p384Sec1TowerType), ("skR", p384ScalarTowerType),
                 ("pkR", p384Sec1TowerType)]
    body     := p384DhkemDecapBody
    retName  := "ss"
    outNames := ["ss", "ok"] }

/-! ## 7. Rust rendering

The rendered bodies wrap the call-only bodies of §6 in zero-initialising
declarations for their locals (`RLetU64Zero` for a `u64`, `RLetZero`
otherwise). -/

/-- Input slots of the `Encap` function. -/
def p384DhkemEncapParams : List Located := [scP384 "skE", sec1P384 "pkR"]

/-- Output slots of the `Encap` function. -/
def p384DhkemEncapResults : List Located :=
  [sec1P384 "enc", scP384 "ss", flagP384 "ok"]

/-- The `Encap` body with its local slots declared. -/
def p384DhkemEncapRustBody : LowCT :=
  p384WithLocals
    [("vs", .TU64), ("vk", .TU64),
     ("Q", p384PointTowerType), ("E", p384PointTowerType),
     ("Z", p384PointTowerType), ("dh", p384ScalarTowerType),
     ("ctx", p384KemContextTowerType), ("prk", p384ScalarTowerType)]
    p384DhkemEncapBody

/-- Input slots of the `Decap` function. -/
def p384DhkemDecapParams : List Located :=
  [sec1P384 "enc", scP384 "skR", sec1P384 "pkR"]

/-- Output slots of the `Decap` function. -/
def p384DhkemDecapResults : List Located := [scP384 "ss", flagP384 "ok"]

/-- The `Decap` body with its local slots declared. -/
def p384DhkemDecapRustBody : LowCT :=
  p384WithLocals
    [("ve", .TU64), ("vs", .TU64),
     ("E", p384PointTowerType), ("Z", p384PointTowerType),
     ("dh", p384ScalarTowerType), ("ctx", p384KemContextTowerType),
     ("prk", p384ScalarTowerType)]
    p384DhkemDecapBody

/-- The Rust source of the DHKEM(P-384) `Encap` function. -/
def p384DhkemEncapRust : String :=
  ppRustFunction "p384_dhkem_encap"
    p384DhkemEncapParams p384DhkemEncapResults p384DhkemEncapRustBody

/-- The Rust source of the DHKEM(P-384) `Decap` function. -/
def p384DhkemDecapRust : String :=
  ppRustFunction "p384_dhkem_decap"
    p384DhkemDecapParams p384DhkemDecapResults p384DhkemDecapRustBody

/-- Write both rendered Rust functions under `bench/p384_ecdsa_rust/gen/`. -/
def emitP384DhkemRust : IO Unit := do
  IO.FS.createDirAll "bench/p384_ecdsa_rust/gen"
  IO.FS.writeFile
    "bench/p384_ecdsa_rust/gen/p384_dhkem_encap.rs" p384DhkemEncapRust
  IO.println "wrote bench/p384_ecdsa_rust/gen/p384_dhkem_encap.rs"
  IO.FS.writeFile
    "bench/p384_ecdsa_rust/gen/p384_dhkem_decap.rs" p384DhkemDecapRust
  IO.println "wrote bench/p384_ecdsa_rust/gen/p384_dhkem_decap.rs"

/-! ## 8. Structural lowering through the owned front -/

/-- The `Encap` body, lowered through the owned front. -/
def p384DhkemEncapJasmin : Cmd := toJasminCmd p384DhkemEncapBody

/-- The `Decap` body, lowered through the owned front. -/
def p384DhkemDecapJasmin : Cmd := toJasminCmd p384DhkemDecapBody

/-- The `Encap` body lowers to eleven Jasmin commands, one per leaf. -/
theorem p384DhkemEncapJasmin_length : p384DhkemEncapJasmin.length = 11 := rfl

/-- Every command the front emits for the `Encap` body is a `Ccall`. -/
theorem p384DhkemEncapJasmin_all_calls :
    p384DhkemEncapJasmin.all
      (fun i => match i with | .Ccall .. => true | _ => false) = true := rfl

/-- The leaf name of each command the front emits for the `Encap` body. -/
theorem p384DhkemEncapJasmin_call_names :
    p384DhkemEncapJasmin.map
        (fun i => match i with | .Ccall _ _ fn _ => fn.name | _ => "") =
      ["p384_scalar_in_range", "p384_sec1_valid", "p384_sec1_decode",
       "p384_scalar_mul_base", "p384_sec1_encode", "p384_scalar_mul",
       "p384_dh_x_be", "p384_kem_context", "dhkem_p384_extract",
       "dhkem_p384_expand", "p384_flag_and"] := rfl

/-- The `Decap` body lowers to nine Jasmin commands, one per leaf. -/
theorem p384DhkemDecapJasmin_length : p384DhkemDecapJasmin.length = 9 := rfl

/-- Every command the front emits for the `Decap` body is a `Ccall`. -/
theorem p384DhkemDecapJasmin_all_calls :
    p384DhkemDecapJasmin.all
      (fun i => match i with | .Ccall .. => true | _ => false) = true := rfl

/-- The leaf name of each command the front emits for the `Decap` body. -/
theorem p384DhkemDecapJasmin_call_names :
    p384DhkemDecapJasmin.map
        (fun i => match i with | .Ccall _ _ fn _ => fn.name | _ => "") =
      ["p384_sec1_valid", "p384_scalar_in_range", "p384_sec1_decode",
       "p384_scalar_mul", "p384_dh_x_be", "p384_kem_context",
       "dhkem_p384_extract", "dhkem_p384_expand", "p384_flag_and"] := rfl

/-! ## 9. Argument and result names

The pins below fix the wire order of each bundle's parameters and results,
which is the order `ppRustFunction` renders into the emitted signature and the
shim crate calls. -/

/-- Parameter order of the `Encap` bundle. -/
example : p384DhkemEncapReified.args.map Prod.fst = ["skE", "pkR"] := rfl

/-- Result order of the `Encap` bundle. -/
example : p384DhkemEncapReified.outNames = ["enc", "ss", "ok"] := rfl

/-- Parameter order of the `Decap` bundle. -/
example : p384DhkemDecapReified.args.map Prod.fst = ["enc", "skR", "pkR"] := rfl

/-- Result order of the `Decap` bundle. -/
example : p384DhkemDecapReified.outNames = ["ss", "ok"] := rfl

/-- The rendered `Encap` signature uses the parameter and result slots of the
    bundle, in the bundle's order. -/
example : p384DhkemEncapParams.map (·.locVar) = p384DhkemEncapReified.args.map Prod.fst ∧
    p384DhkemEncapResults.map (·.locVar) = p384DhkemEncapReified.outNames := ⟨rfl, rfl⟩

/-- The rendered `Decap` signature uses the parameter and result slots of the
    bundle, in the bundle's order. -/
example : p384DhkemDecapParams.map (·.locVar) = p384DhkemDecapReified.args.map Prod.fst ∧
    p384DhkemDecapResults.map (·.locVar) = p384DhkemDecapReified.outNames := ⟨rfl, rfl⟩

end CatCrypt.Crypto.Jasmin.LowCTReflect
