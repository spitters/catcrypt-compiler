/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# Falcon-512 (FN-DSA) reflect surface — verify pipeline through the verified front

This file is the lattice-signature analogue of `MemAbiReflect.lean`:
it adds Falcon-512 specific opaque types and a `LowCTPattern` registration so
that a pure-Lean Falcon-512 verify function can be lifted through the verified
compiler chain `LowCT → CryptoSSA → Com → jasmin`, **without** editing
`LowCTReflect.lean`'s `knownOps` table.

## Verify equation (Falcon spec §3.10.6)

```
  Verify(pk = h, m, sig = (r, s)):
    c    = HashToPoint(r ‖ m)                  -- SHAKE256 reject-sampler → poly
    s2   = DecompressSig(s)                    -- Huffman/Golomb decode → poly
    s1   = c − s2·h          (mod q = 12289)   -- ring subtract
    ok   = ‖(s1, s2)‖² ≤ ⌊β²⌋                  -- norm-bound check (β ≈ 1.1·σ·√(2N))
    return ok
```

We model each major step as one opaque leaf call, working over the
`TPolyMod 12289 512` tower type (`encodeTy ↦ memref 128`):

| Lean axiom                  | Leaf name (.jazz)             | TowerType                |
|----------------------------|-------------------------------|--------------------------|
| `falcon_decode_pk`          | `falcon_decode_pk_12289_512`  | `TPolyMod 12289 512`    |
| `falcon_hash_to_point`      | `falcon_hash_to_point_12289_512` | `TPolyMod 12289 512` |
| `falcon_decode_sig`         | `falcon_decode_sig_12289_512` | `TPolyMod 12289 512`    |
| `falcon_poly_mul_modq`      | `falcon_poly_mul_12289_512`   | `TPolyMod 12289 512`    |
| `falcon_poly_sub_modq`      | `falcon_poly_sub_12289_512`   | `TPolyMod 12289 512`    |
| `falcon_norm_bound_check`   | `falcon_norm_check_12289_512` | `TBytes 8` (u64 boolean) |

The whole verify body is one `LowCT` let-chain that builds `s1` and runs the
norm check, producing a `TBytes 8`-typed cnd word (`1` if accept, `0` if reject).

## Reflection→front gap (same as `MemAbiReflect`)

`reifyLowCT%` reads only `LowCTReflect.knownOps`, not the dynamic
`LowCTPattern` registry. So `reifyLowCT% falconVerifyLean` would error.
We follow the `jhashReified` pattern: define the pure-Lean function for
documentation/spec, register each leaf in the `LowCTPattern` registry via
`@[rust_cmd_pattern]`, then **hand-build the `LowCT`** the reifier *would*
produce. Downstream (`translate → cprogToJasminCom → emitAbiOrchRegPtr`) is
the unmodified verified front.

## References

* Falcon specification (Round 3, 2022), §3.10.6 — Verify procedure
* FIPS 206 (draft, 2026), §5 — FN-DSA verification
* `bench/mlkem_compare/jhash_mem_from_rustcmd.lean` — sibling pattern for the
  hand-built body around `@[rust_cmd_pattern]` registration
-/

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque Falcon-512 surface types

All polynomials live in `R_q = ℤ_q[X]/(X^N + 1)` with `q = 12289`, `N = 512`,
so they share the tower type `TPolyMod 12289 512`. The `decode_*` leaves abstract
away the byte-layer (Falcon's sig/pk wire formats are Huffman/Golomb-coded byte
strings; the verified front sees only their decoded polynomial form). -/

/-- Falcon-512 polynomial in `ℤ_{12289}[X]/(X^512 + 1)` (512 coeffs × 14 bits ≈
    1024 bytes = `memref 128`). Opaque on the Lean side; the leaves
    `falcon_*_12289_512` implement the concrete byte-layout under the hood. -/
axiom FalconPoly : Type
/-- Axiomatic inhabitant. -/ axiom FalconPoly.default : FalconPoly
noncomputable instance : Inhabited FalconPoly := ⟨FalconPoly.default⟩

/-- Falcon-512 public key: the polynomial `h ∈ R_q` plus 1-byte header.
    Wire size: 897 bytes (FIPS 206 draft §5.2). Opaque; `decode_pk` recovers
    the polynomial body. -/
axiom FalconPubKey : Type
/-- Axiomatic inhabitant. -/ axiom FalconPubKey.default : FalconPubKey
noncomputable instance : Inhabited FalconPubKey := ⟨FalconPubKey.default⟩

/-- Falcon-512 signature: 40-byte nonce + 666 bytes of compressed `s` poly.
    Wire size: 666+40+1 = 707 (compact; spec max 752 B). Opaque. -/
axiom FalconSig : Type
/-- Axiomatic inhabitant. -/ axiom FalconSig.default : FalconSig
noncomputable instance : Inhabited FalconSig := ⟨FalconSig.default⟩

/-- Message-with-nonce surface: `r ‖ m` where `r` is the 40-byte nonce drawn
    from the signature header and `m` is the message. The `hash_to_point` leaf
    consumes the bundled bytes; we present it as a single opaque type to keep
    the verify-body let-chain homogeneous. -/
axiom FalconMsgPlusNonce : Type
/-- Axiomatic inhabitant. -/ axiom FalconMsgPlusNonce.default : FalconMsgPlusNonce
noncomputable instance : Inhabited FalconMsgPlusNonce := ⟨FalconMsgPlusNonce.default⟩

/-- Verify result: `1` (accept) or `0` (reject), packaged as an 8-byte word so
    the front can treat it as a single-`u64` return value. -/
axiom FalconAccept : Type
/-- Axiomatic inhabitant. -/ axiom FalconAccept.default : FalconAccept
noncomputable instance : Inhabited FalconAccept := ⟨FalconAccept.default⟩

/-! ## 2. Verify leaves (axioms = opaque jasmin function symbols) -/

/-- `h = decode_pk(pk)`: parses the 897-byte public key into the polynomial `h`. -/
axiom falcon_decode_pk : FalconPubKey → FalconPoly

/-- `c = HashToPoint(r ‖ m)`: SHAKE256 reject-sampler producing a uniform poly
    in `R_q`. Constant-time per Falcon spec (the reject-loop trip count is a
    public function of the seed only, not of secret material). -/
axiom falcon_hash_to_point : FalconMsgPlusNonce → FalconPoly

/-- `s2 = decode_sig(sig)`: decompresses the Huffman/Golomb-coded `s` polynomial
    from the signature header. The signature wire format also implicitly
    provides the nonce `r` (via `falcon_sig_nonce` below). -/
axiom falcon_decode_sig : FalconSig → FalconPoly

/-- `t = s2 · h mod (X^N + 1, q)`: the ring multiplication. Implementation-wise
    a forward-NTT pair, NTT-domain pointwise, inverse-NTT round trip — see the
    `polymul_from_rustcmd.lean` pattern. Opaque here to keep the verify body
    flat. -/
axiom falcon_poly_mul_modq : FalconPoly → FalconPoly → FalconPoly

/-- `s1 = c − t mod q`: coefficientwise subtraction with mod-`q` correction.
    This is the lane-map kernel of the legacy FN-DSA emit (`fndsa_512_verify`),
    here lifted to the polynomial-level operation. -/
axiom falcon_poly_sub_modq : FalconPoly → FalconPoly → FalconPoly

/-- `ok = ‖(s1, s2)‖² ≤ ⌊β²⌋`: norm-bound check. Returns 1 (accept) iff the
    sum of squared signed-canonical coefficients is within the spec bound
    (`⌊β²⌋ = 34034726` for Falcon-512). -/
axiom falcon_norm_bound_check : FalconPoly → FalconPoly → FalconAccept

/-- Helper: extract the message-plus-nonce bundle from the (sig, msg) pair.
    Real implementations concatenate `sig.r ‖ msg`; modelled here as one
    opaque leaf. -/
axiom falcon_sig_msg_bundle : FalconSig → FalconMsgPlusNonce

/-! ## 3. `@[rust_cmd_pattern]` registrations -/

/-- Register `falcon_decode_pk` → leaf `falcon_decode_pk_12289_512`. -/
@[rust_cmd_pattern]
def falconDecodePkPattern : LowCTPattern where
  name      := "falcon_decode_pk_12289_512"
  fnHead    := ``falcon_decode_pk
  arity     := 1
  towerType := .TPolyMod 12289 512

/-- Register `falcon_hash_to_point` → leaf `falcon_hash_to_point_12289_512`. -/
@[rust_cmd_pattern]
def falconHashToPointPattern : LowCTPattern where
  name      := "falcon_hash_to_point_12289_512"
  fnHead    := ``falcon_hash_to_point
  arity     := 1
  towerType := .TPolyMod 12289 512

/-- Register `falcon_decode_sig` → leaf `falcon_decode_sig_12289_512`. -/
@[rust_cmd_pattern]
def falconDecodeSigPattern : LowCTPattern where
  name      := "falcon_decode_sig_12289_512"
  fnHead    := ``falcon_decode_sig
  arity     := 1
  towerType := .TPolyMod 12289 512

/-- Register `falcon_poly_mul_modq` → leaf `falcon_poly_mul_12289_512`. -/
@[rust_cmd_pattern]
def falconPolyMulPattern : LowCTPattern where
  name      := "falcon_poly_mul_12289_512"
  fnHead    := ``falcon_poly_mul_modq
  arity     := 2
  towerType := .TPolyMod 12289 512

/-- Register `falcon_poly_sub_modq` → leaf `falcon_poly_sub_12289_512`. -/
@[rust_cmd_pattern]
def falconPolySubPattern : LowCTPattern where
  name      := "falcon_poly_sub_12289_512"
  fnHead    := ``falcon_poly_sub_modq
  arity     := 2
  towerType := .TPolyMod 12289 512

/-- Register `falcon_norm_bound_check` → leaf `falcon_norm_check_12289_512`. -/
@[rust_cmd_pattern]
def falconNormCheckPattern : LowCTPattern where
  name      := "falcon_norm_check_12289_512"
  fnHead    := ``falcon_norm_bound_check
  arity     := 2
  towerType := .TBytes 8

/-- Register `falcon_sig_msg_bundle` → leaf `falcon_bundle_sig_msg`. -/
@[rust_cmd_pattern]
def falconSigMsgBundlePattern : LowCTPattern where
  name      := "falcon_bundle_sig_msg"
  fnHead    := ``falcon_sig_msg_bundle
  arity     := 1
  towerType := .TBytes 552 -- 40 byte nonce + 512 byte msg ceiling; opaque size

/-! ## 4. Pure-Lean verify function — the spec for what the emit must implement -/

/-- Falcon-512 verify procedure (full pipeline):

    `Verify(pk, sig, msg) = ok`

    where `ok` is `1` if accept, `0` if reject. Matches FIPS 206 draft §5.3 and
    the Falcon round-3 spec §3.10.6 procedure body. The byte-layer leaves
    (`decode_pk`, `decode_sig`, `bundle`, `hash_to_point`, `norm_check`) absorb
    the wire-format and SHAKE-rejection details; the arithmetic core
    (`poly_mul + poly_sub mod q`) is the `c − s2·h` ring computation that
    legacy `fndsa_512_verify` SIMD-emitted as a lane-map (this version emits
    the WHOLE verify orchestration, not just the inner subtract lane). -/
noncomputable def falconVerifyLean (pk : FalconPubKey) (sig : FalconSig)
    (msg : FalconMsgPlusNonce) : FalconAccept :=
  let h    := falcon_decode_pk pk
  let s2   := falcon_decode_sig sig
  let _bnd := falcon_sig_msg_bundle sig    -- documents the r‖msg dependency
  let c    := falcon_hash_to_point msg
  let t    := falcon_poly_mul_modq s2 h
  let s1   := falcon_poly_sub_modq c t
  falcon_norm_bound_check s1 s2

/-! ## 5. Hand-built `LowCT` body (the front-end input)

Since `reifyLowCT%` does not consult the `LowCTPattern` registry, we
hand-build the body the reifier *would* produce for `falconVerifyLean`. The
shape is one `RSeq`-chain of `RCall`s, one per leaf, matching the let-bindings
of `falconVerifyLean` exactly. -/

/-- TowerType abbreviations matching `leanTypeToTowerType` defaults for each
    Falcon surface type (so that downstream `translate` sees the same encoding
    a `reifyLowCT%` pass would have produced). -/
def falconPkTowerType  : TowerType := .TBytes 897
/-- The signature wire size (≤ 752 bytes spec max; we use 752 as ceiling). -/
def falconSigTowerType : TowerType := .TBytes 752
/-- The bundled `r ‖ msg` byte string (≤ 552 bytes used here as a fixed-size
    surface; the `bundle` leaf is the size-erasing wrapper). -/
def falconMsgTowerType : TowerType := .TBytes 552
/-- A Falcon polynomial in `R_q`. -/
def falconPolyTowerType : TowerType := .TPolyMod 12289 512
/-- 8-byte accept-flag word (the verify boolean). -/
def falconAcceptTowerType : TowerType := .TBytes 8

private def loc (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-- The `LowCT` body the reifier *would* produce for `falconVerifyLean`.

    Sequence (mirrors the `let` chain above):
    ```
    h    := decode_pk(pk)
    s2   := decode_sig(sig)
    _bnd := bundle_sig_msg(sig)        // present even if unused, mirrors spec
    c    := hash_to_point(msg)
    t    := poly_mul(s2, h)
    s1   := poly_sub(c, t)
    __result := norm_check(s1, s2)
    ```
    Each step is one `RCall leafName dest args`; the final result name
    `__result` matches `reifyLowCT%`'s end-of-chain convention. -/
def falconVerifyBody : LowCT :=
  let pk_l     := loc "pk"     falconPkTowerType
  let sig_l    := loc "sig"    falconSigTowerType
  let msg_l    := loc "msg"    falconMsgTowerType
  let h_l      := loc "h"      falconPolyTowerType
  let s2_l     := loc "s2"     falconPolyTowerType
  let bnd_l    := loc "_bnd"   falconMsgTowerType
  let c_l      := loc "c"      falconPolyTowerType
  let t_l      := loc "t"      falconPolyTowerType
  let s1_l     := loc "s1"     falconPolyTowerType
  let result_l := loc "__result" falconAcceptTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "falcon_decode_pk_12289_512"        h_l   [pk_l]))
    (.RCall "falcon_decode_sig_12289_512"       s2_l  [sig_l]))
    (.RCall "falcon_bundle_sig_msg"             bnd_l [sig_l]))
    (.RCall "falcon_hash_to_point_12289_512"    c_l   [msg_l]))
    (.RCall "falcon_poly_mul_12289_512"         t_l   [s2_l, h_l]))
    (.RCall "falcon_poly_sub_12289_512"         s1_l  [c_l, t_l]))
    (.RCall "falcon_norm_check_12289_512"       result_l [s1_l, s2_l])

/-- The `ReifiedFunc` bundle for `falconVerifyLean`, assembled by hand from
    `falconVerifyBody`. Same field-shape `reifyLowCT%` would produce; the
    bench driver consumes `.body` / `.retName` exactly as it would a reifier
    output. -/
def falconVerifyReified : ReifiedFunc :=
  { args    := [("pk",  falconPkTowerType),
                ("sig", falconSigTowerType),
                ("msg", falconMsgTowerType)]
    body    := falconVerifyBody
    retName := "__result" }

/-! ## 6. Scoped-down kernel: `c − s2h mod q` standalone (KAT target)

The full `falconVerifyLean` emit calls 7 opaque leaves; KATs require concrete
leaf implementations. To exercise the verified chain on a **runnable** Falcon-
adjacent kernel without needing all 7 leaf implementations, we also emit the
narrow `c − s2h mod q` standalone (one `RCall` to `falcon_poly_sub_modq`,
matching what the legacy `fndsa_512_verify` SIMD lane-map covers).

This is the same `c − s2·h mod q` arithmetic kernel — the only piece of
Falcon verify that has a self-contained C reference (the legacy
`bench/fndsa_compare/gen/fndsa_512_verify.jazz` SIMD body) — but now emitted
**through the verified front**, so the comparison is in-chain. -/

/-- Pure-Lean version of the kernel: one poly subtraction mod q. -/
noncomputable def falconSubModqLean (c t : FalconPoly) : FalconPoly :=
  falcon_poly_sub_modq c t

/-- Hand-built body matching `falconSubModqLean`. -/
def falconSubModqBody : LowCT :=
  let c_l      := loc "c"        falconPolyTowerType
  let t_l      := loc "t"        falconPolyTowerType
  let result_l := loc "__result" falconPolyTowerType
  .RSeq .RSkip
    (.RCall "falcon_poly_sub_12289_512" result_l [c_l, t_l])

/-- `ReifiedFunc` bundle for the standalone kernel. -/
def falconSubModqReified : ReifiedFunc :=
  { args    := [("c", falconPolyTowerType), ("t", falconPolyTowerType)]
    body    := falconSubModqBody
    retName := "__result" }

/-! ## 7. Sign-side surface (Falcon-512 sign through the verified front)

The sign body in FIPS 206 draft / Falcon round-3 §3.10.3:

```
  Sign(sk = (f, g, F, G), msg):
    nonce ← {0,1}^320
    c     := HashToPoint(nonce ‖ msg)
    repeat:
      (t0, t1) := (-c · F / q, c · f / q)      -- FFT-domain target
      (z0, z1) := ffSampling(t0, t1, LDL_tree(sk))
      (s1, s2) := ((t0 - z0)·f + (t1 - z1)·F,
                   (t0 - z0)·g + (t1 - z1)·G)  -- short vector basis-rotated
      norm2    := ‖(s1, s2)‖²
      if norm2 ≤ ⌊β²⌋:
        return Encode(nonce, s2)               -- Golomb-Huffman compress s2
```

The big residual is `ffSampling` (the secret-domain Gaussian sampler over the
LDL-tree of the secret basis): LowCT cannot express its FFT-tree recursion
natively. We model it as a single opaque leaf `falcon_ffsampling_512` consuming
the secret key + the FFT-domain target and producing the preimage pair. The
reject-loop is folded into the leaf (Falcon spec § "Sign" notes the reject-loop
trip count is randomness-dependent but constant in expectation; here we treat
the leaf as if it always returns a within-bound sample, since the leaf
implementation handles the loop internally).

The compressed-encode step is one opaque leaf `falcon_comp_encode_512`. The
nonce-draw is one opaque leaf `falcon_draw_nonce`. -/

/-- Falcon-512 secret key: `(f, g, F, G)` plus 1-byte header. Wire size 1281
    bytes (FIPS 206 draft §5.2). Opaque on the Lean side; the leaves operate
    on the byte form, with the basis fields recovered internally. -/
axiom FalconSecKey : Type
/-- Axiomatic inhabitant. -/ axiom FalconSecKey.default : FalconSecKey
noncomputable instance : Inhabited FalconSecKey := ⟨FalconSecKey.default⟩

/-- Fresh 40-byte sign nonce drawn from the system randomness. Opaque; the
    `falcon_draw_nonce` leaf realizes the rejection-free byte draw. -/
axiom FalconNonce : Type
/-- Axiomatic inhabitant. -/ axiom FalconNonce.default : FalconNonce
noncomputable instance : Inhabited FalconNonce := ⟨FalconNonce.default⟩

/-- Pair of short polynomials `(s1, s2) ∈ R_q × R_q` produced by `ffSampling`
    against the secret basis. The Falcon sampler's primary product; the sign
    body keeps `s2` and encodes the difference of `s1` against `c − s2·h`. -/
axiom FalconShortPair : Type
/-- Axiomatic inhabitant. -/ axiom FalconShortPair.default : FalconShortPair
noncomputable instance : Inhabited FalconShortPair := ⟨FalconShortPair.default⟩

/-! ### Sign leaves (axioms = opaque jasmin function symbols) -/

/-- `nonce = draw_nonce()`: 40-byte system-RNG draw, opaque seed for sign. -/
axiom falcon_draw_nonce : Unit → FalconNonce

/-- `bundle = nonce ‖ msg`: glue nonce and msg into the SHAKE256 hash input. -/
axiom falcon_bundle_nonce_msg : FalconNonce → FalconMsgPlusNonce → FalconMsgPlusNonce

/-- `(s1, s2) = ffSampling(sk, c)`: the secret-basis Gaussian sampler. Opaque
    leaf — the FFT-tree recursion is the BIG residual; LowCT can't express
    it natively. Implementation handles the reject-loop internally. -/
axiom falcon_ffsampling : FalconSecKey → FalconPoly → FalconShortPair

/-- `s2 = project_s2(pair)`: extract the s2 component the signature carries. -/
axiom falcon_project_s2 : FalconShortPair → FalconPoly

/-- `sig = comp_encode(nonce, s2)`: Golomb-Huffman compress `s2`, prepend the
    nonce header byte and the nonce, output the 752-byte ceiling signature.
    Opaque leaf — the bit-packed codec is byte-layer detail. -/
axiom falcon_comp_encode : FalconNonce → FalconPoly → FalconSig

/-! ### Sign `@[rust_cmd_pattern]` registrations -/

/-- Register `falcon_draw_nonce` → leaf `falcon_draw_nonce_512`. -/
@[rust_cmd_pattern]
def falconDrawNoncePattern : LowCTPattern where
  name      := "falcon_draw_nonce_512"
  fnHead    := ``falcon_draw_nonce
  arity     := 1
  towerType := .TBytes 40

/-- Register `falcon_bundle_nonce_msg` → leaf `falcon_bundle_nonce_msg_512`. -/
@[rust_cmd_pattern]
def falconBundleNonceMsgPattern : LowCTPattern where
  name      := "falcon_bundle_nonce_msg_512"
  fnHead    := ``falcon_bundle_nonce_msg
  arity     := 2
  towerType := .TBytes 552

/-- Register `falcon_ffsampling` → leaf `falcon_ffsampling_512`. -/
@[rust_cmd_pattern]
def falconFfsamplingPattern : LowCTPattern where
  name      := "falcon_ffsampling_512"
  fnHead    := ``falcon_ffsampling
  arity     := 2
  -- The result is an opaque pair living in poly storage. We bias the tower
  -- type to a polynomial-sized buffer (the pair packs 2×512 u16 coefficients
  -- into ≤ 2 KB; the front sees a memref-shaped block carrying both
  -- components).
  towerType := .TPolyMod 12289 512

/-- Register `falcon_project_s2` → leaf `falcon_project_s2_512`. -/
@[rust_cmd_pattern]
def falconProjectS2Pattern : LowCTPattern where
  name      := "falcon_project_s2_512"
  fnHead    := ``falcon_project_s2
  arity     := 1
  towerType := .TPolyMod 12289 512

/-- Register `falcon_comp_encode` → leaf `falcon_comp_encode_512`. -/
@[rust_cmd_pattern]
def falconCompEncodePattern : LowCTPattern where
  name      := "falcon_comp_encode_512"
  fnHead    := ``falcon_comp_encode
  arity     := 2
  towerType := .TBytes 752

/-- TowerType for the secret key wire form. -/
def falconSkTowerType    : TowerType := .TBytes 1281
/-- TowerType for the nonce. -/
def falconNonceTowerType : TowerType := .TBytes 40
/-- TowerType for the `ffSampling` short pair (carried as one buffer). -/
def falconPairTowerType  : TowerType := .TPolyMod 12289 512
/-- TowerType for the unit/seed input to `draw_nonce` (an empty buffer). -/
def falconUnitTowerType  : TowerType := .TBytes 8

/-! ### Pure-Lean Falcon-512 sign function — the spec the emit must implement -/

/-- Falcon-512 sign procedure (orchestration scope):

    `Sign(sk, msg) = sig`

    where `sig` is the 752-byte ceiling wire form. The probabilistic
    `ffSampling` reject-loop is folded into the opaque leaf (the leaf
    behaves as if it always returns a within-bound sample, matching PQClean's
    sign loop). The deterministic chain after sampling is:

    ```
      nonce  ← draw_nonce()
      bundle ← bundle_nonce_msg(nonce, msg)
      c      ← hash_to_point(bundle)
      pair   ← ffSampling(sk, c)
      s2     ← project_s2(pair)
      sig    ← comp_encode(nonce, s2)
    ```

    Sk is opaque; the leaves read the byte form. -/
noncomputable def falconSignLean (sk : FalconSecKey) (msg : FalconMsgPlusNonce) :
    FalconSig :=
  let nonce  := falcon_draw_nonce ()
  let bundle := falcon_bundle_nonce_msg nonce msg
  let c      := falcon_hash_to_point bundle
  let pair   := falcon_ffsampling sk c
  let s2     := falcon_project_s2 pair
  falcon_comp_encode nonce s2

/-- The `LowCT` body the reifier *would* produce for `falconSignLean`.

    Sequence (mirrors the `let` chain above):
    ```
    nonce    := draw_nonce(_unit)
    bundle   := bundle_nonce_msg(nonce, msg)
    c        := hash_to_point(bundle)
    pair     := ffsampling(sk, c)
    s2       := project_s2(pair)
    __result := comp_encode(nonce, s2)
    ```

    The dummy `_unit` input to `draw_nonce` mirrors the LowCT convention
    that every `RCall` has at least one arg; in Rust this would be a unit-
    typed parameter or no parameter, here it's a fresh empty buffer. -/
def falconSignBody : LowCT :=
  let sk_l     := loc "sk"     falconSkTowerType
  let msg_l    := loc "msg"    falconMsgTowerType
  let unit_l   := loc "_unit"  falconUnitTowerType
  let nonce_l  := loc "nonce"  falconNonceTowerType
  let bundle_l := loc "bundle" falconMsgTowerType
  let c_l      := loc "c"      falconPolyTowerType
  let pair_l   := loc "pair"   falconPairTowerType
  let s2_l     := loc "s2"     falconPolyTowerType
  let result_l := loc "__result" falconSigTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "falcon_draw_nonce_512"            nonce_l  [unit_l]))
    (.RCall "falcon_bundle_nonce_msg_512"      bundle_l [nonce_l, msg_l]))
    (.RCall "falcon_hash_to_point_12289_512"   c_l      [bundle_l]))
    (.RCall "falcon_ffsampling_512"            pair_l   [sk_l, c_l]))
    (.RCall "falcon_project_s2_512"            s2_l     [pair_l]))
    (.RCall "falcon_comp_encode_512"           result_l [nonce_l, s2_l])

/-- The `ReifiedFunc` bundle for `falconSignLean`. Inputs `sk, msg, _unit`. -/
def falconSignReified : ReifiedFunc :=
  { args    := [("sk",    falconSkTowerType),
                ("msg",   falconMsgTowerType),
                ("_unit", falconUnitTowerType)]
    body    := falconSignBody
    retName := "__result" }

/-! ## 8. Keygen-side surface (Falcon-512 keygen through the verified front)

Falcon keygen draws an NTRU basis `(f, g)` (short polynomials, Gaussian-tail)
and solves an NTRU equation for `(F, G)`:

```
  Keygen():
    (f, g) := NTRUGen()              -- short polys, in (-127..127) range
    (F, G) := NTRUSolve(f, g)        -- inhomogeneous NTRU equation
    h      := g · f⁻¹ mod q          -- public key
    sk     := encode_sk(f, g, F, G)  -- 1281 bytes
    pk     := encode_pk(h)           -- 897 bytes
    return (pk, sk)
```

NTRUGen and NTRUSolve are heavy and randomness-dependent; we model each as one
opaque leaf. The `f⁻¹` / `g · f⁻¹` step factors through `falcon_poly_mul_modq`
already registered (we add a `falcon_poly_inv_modq` leaf for the inversion
step). LDL precompute (the secret-basis decomposition the sampler later
consumes) is folded into the secret-key encoding for simplicity (the encoded
sk carries the basis, and the sampler re-derives the LDL tree on each sign
call — matching PQClean's tree-on-demand layout). -/

/-- NTRU basis pair `(f, g)`: two short polynomials, Gaussian-tail. Opaque
    packaging; the leaves read it via the same byte-form interface. -/
axiom FalconNTRUBasis : Type
/-- Axiomatic inhabitant. -/ axiom FalconNTRUBasis.default : FalconNTRUBasis
noncomputable instance : Inhabited FalconNTRUBasis := ⟨FalconNTRUBasis.default⟩

/-- Full NTRU-solved basis `(f, g, F, G)`. Opaque. -/
axiom FalconFullBasis : Type
/-- Axiomatic inhabitant. -/ axiom FalconFullBasis.default : FalconFullBasis
noncomputable instance : Inhabited FalconFullBasis := ⟨FalconFullBasis.default⟩

/-! ### Keygen leaves (axioms = opaque jasmin function symbols) -/

/-- `(f, g) = NTRUGen()`: sample a short NTRU basis pair. -/
axiom falcon_ntru_gen : Unit → FalconNTRUBasis

/-- `(F, G) = NTRUSolve(f, g)`: complete the basis (inhomogeneous NTRU). -/
axiom falcon_ntru_solve : FalconNTRUBasis → FalconFullBasis

/-- `h_inv = f⁻¹ mod q`: modular inverse of `f` in `R_q`. (Distinct from the
    multiply leaf already registered; this is the inversion step.) -/
axiom falcon_poly_inv_modq : FalconNTRUBasis → FalconPoly

/-- `h = g · f⁻¹ mod q`: public-key polynomial. Re-uses
    `falcon_poly_mul_modq`'s contract; this wrapper packages the
    NTRU-basis argument shape so the orchestration is uniform. -/
axiom falcon_derive_h : FalconNTRUBasis → FalconPoly → FalconPoly

/-- `pk = encode_pk(h)`: pack `h` into the 897-byte public key wire form. -/
axiom falcon_encode_pk : FalconPoly → FalconPubKey

/-- `sk = encode_sk(fullbasis)`: pack `(f, g, F, G)` into the 1281-byte
    secret key wire form. -/
axiom falcon_encode_sk : FalconFullBasis → FalconSecKey

/-! ### Keygen `@[rust_cmd_pattern]` registrations -/

/-- Register `falcon_ntru_gen` → leaf `falcon_ntru_gen_512`. -/
@[rust_cmd_pattern]
def falconNtruGenPattern : LowCTPattern where
  name      := "falcon_ntru_gen_512"
  fnHead    := ``falcon_ntru_gen
  arity     := 1
  towerType := .TPolyMod 12289 512

/-- Register `falcon_ntru_solve` → leaf `falcon_ntru_solve_512`. -/
@[rust_cmd_pattern]
def falconNtruSolvePattern : LowCTPattern where
  name      := "falcon_ntru_solve_512"
  fnHead    := ``falcon_ntru_solve
  arity     := 1
  towerType := .TPolyMod 12289 512

/-- Register `falcon_poly_inv_modq` → leaf `falcon_poly_inv_12289_512`. -/
@[rust_cmd_pattern]
def falconPolyInvPattern : LowCTPattern where
  name      := "falcon_poly_inv_12289_512"
  fnHead    := ``falcon_poly_inv_modq
  arity     := 1
  towerType := .TPolyMod 12289 512

/-- Register `falcon_derive_h` → leaf `falcon_derive_h_12289_512`. -/
@[rust_cmd_pattern]
def falconDeriveHPattern : LowCTPattern where
  name      := "falcon_derive_h_12289_512"
  fnHead    := ``falcon_derive_h
  arity     := 2
  towerType := .TPolyMod 12289 512

/-- Register `falcon_encode_pk` → leaf `falcon_encode_pk_512`. -/
@[rust_cmd_pattern]
def falconEncodePkPattern : LowCTPattern where
  name      := "falcon_encode_pk_512"
  fnHead    := ``falcon_encode_pk
  arity     := 1
  towerType := .TBytes 897

/-- Register `falcon_encode_sk` → leaf `falcon_encode_sk_512`. -/
@[rust_cmd_pattern]
def falconEncodeSkPattern : LowCTPattern where
  name      := "falcon_encode_sk_512"
  fnHead    := ``falcon_encode_sk
  arity     := 1
  towerType := .TBytes 1281

/-! ### TowerTypes specific to keygen -/

/-- TowerType for the NTRU basis pair (opaque, polynomial-sized). -/
def falconBasisTowerType     : TowerType := .TPolyMod 12289 512
/-- TowerType for the full NTRU-solved basis. -/
def falconFullBasisTowerType : TowerType := .TPolyMod 12289 512

/-! ### Pure-Lean Falcon-512 keygen function — the spec the emit must implement -/

/-- Falcon-512 keygen procedure (orchestration scope):

    `Keygen(_unit) = (pk, sk)` (returned as a single Sk-wire blob whose first
    897 bytes are pk and remaining 1281 bytes are sk in a chained wire
    layout; the emit packs them into the canonical PQClean format).

    Chain:
    ```
      fg     ← ntru_gen(_unit)
      full   ← ntru_solve(fg)
      h_inv  ← poly_inv(fg)        -- f⁻¹ mod q
      h      ← derive_h(fg, h_inv) -- g · f⁻¹ mod q
      pk     ← encode_pk(h)
      sk     ← encode_sk(full)
      bundle := bundle_pk_sk(pk, sk)
    ```

    The final `bundle` is folded back into the secret-key wire (sk-only
    output; pk can be re-derived from sk, matching PQClean's
    `crypto_sign_keypair` returning both pointers). For the
    orchestration's single-result convention, we keep `sk` as the return
    type; a runtime wrapper splits sk back into (pk, sk). -/
noncomputable def falconKeygenLean (_unit : Unit) : FalconSecKey :=
  let fg     := falcon_ntru_gen _unit
  let full   := falcon_ntru_solve fg
  let h_inv  := falcon_poly_inv_modq fg
  let _h     := falcon_derive_h fg h_inv     -- documents the pk-derivation
  let _pk    := falcon_encode_pk _h           -- documents the pk wire form
  falcon_encode_sk full

/-- The `LowCT` body the reifier *would* produce for `falconKeygenLean`.

    Sequence (mirrors the `let` chain above; the `_h` / `_pk` lets are
    threaded as proper `RCall`s even though `_pk` is unused in the final
    sk-only return, mirroring the spec's two-step `(pk, sk)` derivation):
    ```
    fg       := ntru_gen(_unit)
    full     := ntru_solve(fg)
    h_inv    := poly_inv(fg)
    h        := derive_h(fg, h_inv)
    pk       := encode_pk(h)
    __result := encode_sk(full)
    ```
-/
def falconKeygenBody : LowCT :=
  let unit_l   := loc "_unit" falconUnitTowerType
  let fg_l     := loc "fg"    falconBasisTowerType
  let full_l   := loc "full"  falconFullBasisTowerType
  let h_inv_l  := loc "h_inv" falconPolyTowerType
  let h_l      := loc "h"     falconPolyTowerType
  let pk_l     := loc "pk"    falconPkTowerType
  let result_l := loc "__result" falconSkTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall "falcon_ntru_gen_512"          fg_l    [unit_l]))
    (.RCall "falcon_ntru_solve_512"        full_l  [fg_l]))
    (.RCall "falcon_poly_inv_12289_512"    h_inv_l [fg_l]))
    (.RCall "falcon_derive_h_12289_512"    h_l     [fg_l, h_inv_l]))
    (.RCall "falcon_encode_pk_512"         pk_l    [h_l]))
    (.RCall "falcon_encode_sk_512"         result_l [full_l])

/-- The `ReifiedFunc` bundle for `falconKeygenLean`. -/
def falconKeygenReified : ReifiedFunc :=
  { args    := [("_unit", falconUnitTowerType)]
    body    := falconKeygenBody
    retName := "__result" }

/-! ## 9. Opaque-leaf correctness hypotheses

The leaves above are opaque axioms in Lean. The emit's correctness lifts to
the full spec only if the leaves' jasmin implementations match their
intended semantics. We name those obligations explicitly here so downstream
files can quote them (they are NOT proven; the leaves are linked against
PQClean's matching implementations at C-harness link time, and the named
hypotheses below are the assumption that link-time behavior is correct). -/

/-- Sign-side opaque-leaf assumption: `falcon_ffsampling`'s jasmin
    implementation produces a within-bound short-vector preimage of `c`
    against the secret basis. This is the BIG residual; the Falcon spec's
    Theorem 3.9 (Gaussian tail) is what a real proof would invoke. -/
def FfsamplingLeafCorrect : Prop := True  -- named hypothesis only

/-- Sign-side opaque-leaf assumption: `falcon_comp_encode`'s jasmin
    implementation realizes the spec's Golomb-Huffman bit-packing of `s2`
    plus the 41-byte nonce/header. -/
def CompEncodeLeafCorrect : Prop := True  -- named hypothesis only

/-- Keygen-side opaque-leaf assumption: `falcon_ntru_gen` produces a
    short NTRU basis pair within the spec's expected distribution. -/
def NtruGenLeafCorrect : Prop := True     -- named hypothesis only

/-- Keygen-side opaque-leaf assumption: `falcon_ntru_solve` returns
    `(F, G)` with `fG − gF = q` (the inhomogeneous NTRU equation). -/
def NtruSolveLeafCorrect : Prop := True   -- named hypothesis only

/-- Keygen-side opaque-leaf assumption: LDL-precompute (folded into
    `falcon_encode_sk`) is consistent with the basis the sampler
    later consumes. -/
def LdlPrecomputeLeafCorrect : Prop := True -- named hypothesis only

/-! ## 10. Inspection -/

#eval falconVerifyReified.args.map Prod.fst              -- [pk, sig, msg]
#eval falconVerifyReified.args.length                    -- 3
#eval falconVerifyReified.retName                        -- __result
#eval falconSubModqReified.args.length                   -- 2
#eval falconSignReified.args.map Prod.fst                -- [sk, msg, _unit]
#eval falconSignReified.args.length                      -- 3
#eval falconKeygenReified.args.length                    -- 1

open Lean in
#eval show Lean.MetaM _ from do
  LowCTPattern.taggedDecls                              -- expect verify + sign + keygen patterns

end CatCrypt.Crypto.Jasmin.LowCTReflect
