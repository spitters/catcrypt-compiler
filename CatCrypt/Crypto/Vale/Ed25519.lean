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
public meta import CatCrypt.Crypto.Vale.LeafLeakage
public import CatCrypt.Crypto.Vale.LeafLeakage


@[expose] public section
set_option autoImplicit false

/-!
# Vale-verified Ed25519 leaf (HACL\* `Hacl_Ed25519_{sign,verify}`)

This module declares the HACL\* Vale-verified Ed25519 signing and
verification primitives — RFC 8032 EdDSA over edwards25519, built on
the Vale-extracted Curve25519 field arithmetic in
`curve25519-x86_64-linux.S` plus the Vale-extracted SHA-512 in
`sha512-x86_64-linux.S` — as opaque verified-CT leaves for CatCrypt's
verified front, following the established extCall pattern
(Jasmin.LowCT `RCall`).

## Pilot scope (Vale-leaf adoption, Edwards-form curve sweep)

Edwards-form sibling of the `Vale/Curve25519.lean` (Montgomery-form,
X25519) leaf.  This is the wave-2 leaf for the Ed25519 EdDSA signature
scheme, paired with the AUCurves Coq-extracted Jasmin stub list
`ed25519_sign_stubs_jasmin_extracted.{ml,mli}`
(which decomposes the RFC 8032 Ed25519 sign path into the per-leaf
extern stubs `sha512_64`, `clamp_64`, `ed25519_scalarmult_base`,
`ed25519_compress`, `scalar_reduce`, `scalar_muladd`, and the eight
region-copy `memmove_*` helpers).

At the verified-front level we adopt the **whole HACL\* primitive**
(`Hacl_Ed25519_sign` / `Hacl_Ed25519_verify`) rather than the
AUCurves-decomposed leaf list — these are the natural Vale-leaf
boundaries cited by HACL\*'s F\* proof.  The AUCurves decomposition is
the canonical surface against which the verified-front's `LowCT`
denotation is checked (it factors through the same primitives that
HACL\*'s C driver consumes).

## Architectural claim (the composition)

```
CatCrypt(glue) + Vale/HACL\*(Ed25519 leaves)
    via the extCall denotation at the Veir/Jasmin extCall boundary
    -> verified-CT pipeline
```

CatCrypt's verified front discharges the orchestration; the leaves'
denotations match HACL\*'s F\* proofs (cited below); CT is inherited
from the Vale taint-tracking proof on the field arithmetic plus
HACL\*'s secret-independence proof on the EdDSA driver.

## The HACL\* / Vale provenance

* **C drivers**: `Hacl_Ed25519.c` (libcrux/HACL*),
  exporting the C symbols `Hacl_Ed25519_sign`, `Hacl_Ed25519_verify`,
  `Hacl_Ed25519_secret_to_public`, `Hacl_Ed25519_expand_keys`,
  `Hacl_Ed25519_sign_expanded`.  The drivers compose the Vale-verified
  Curve25519 field arithmetic, the Vale-verified SHA-512 compression,
  and the EdDSA-specific scalar/point arithmetic (encode/decode,
  scalar_muladd, scalar_reduce, the Edwards group law).
* **Vale assembly**: the field-arithmetic and SHA-512 primitives are
  the Vale-extracted `*_e` symbols in
  `vale/src/curve25519-x86_64-linux.S` and
  `vale/src/sha512-x86_64-linux.S`.
* **F\* / Vale proof**: the EdDSA driver is proved functionally
  correct in F\* against `Spec.Ed25519` (Polubelova et al. CHES 2020,
  on top of Bond et al. PLDI 2017 for the Vale field arithmetic);
  RFC 8032 §5.1 (Ed25519 pure mode).
* **NIST CAVP / RFC 8032 §7.1**: HACL\*'s `Hacl_Ed25519_*` matches
  every RFC 8032 §7.1 published test vector byte-for-byte (validated
  in `bench/ed25519_compare/conform_ed25519_vale.c`).

## Leaf C signatures

```c
extern void Hacl_Ed25519_sign(uint8_t *signature,
                              uint8_t *private_key,
                              uint32_t msg_len, uint8_t *msg);

extern bool Hacl_Ed25519_verify(uint8_t *public_key,
                                uint32_t msg_len, uint8_t *msg,
                                uint8_t *signature);
```

That is:
* `signature = Ed25519.Sign(private_key, msg)` (RFC 8032 §5.1.6) into
  a 64-byte output buffer.
* `Ed25519.Verify(public_key, msg, signature)` (RFC 8032 §5.1.7)
  returning `true` iff the signature is valid.

## Trust delta (what we trust ABOVE CatCrypt's normal axiom set)

By adopting these leaves we additionally trust:

1. **Vale_Hacl_Ed25519_sign_denote** — the leaf computes
   `Spec.Ed25519.sign` per RFC 8032 §5.1.6.  Sourced from HACL\*'s
   F\* proof in `Hacl.Ed25519.fst` and the Vale field-arithmetic /
   SHA-512 proofs.

2. **Vale_Hacl_Ed25519_sign_CT** — the leaf is constant-time in the
   secret seed and the message buffer.  Sourced from HACL\*'s
   secret-independence proof on the EdDSA driver plus the Vale
   taint-tracking proofs on the underlying primitives.

3. **Vale_Hacl_Ed25519_verify_denote** — the leaf returns the
   RFC 8032 verification result.  Sourced from HACL\*'s F\* proof
   against `Spec.Ed25519.verify`.

4. **Vale_Hacl_Ed25519_verify_not_CT** — the verify leaf is variable
   time: the scalar range check and the point equality test
   declassify limbs and branch on them.  All three of its arguments
   are public, so this is licensed by the public-taint policy, and
   the reject side is recorded rather than a constant-time claim.

5. **Symbol identity at link time** — standard C-linker trust on the
   `Hacl_Ed25519_*` exports from `Hacl_Ed25519.c`.

The trust delta is **strictly smaller** than the all-our-emit path
when the alternative is the ADX-Edwards prototype in
`bench/ed25519_adx_compare/` (Lean-spec → C transliteration → gcc),
because:

* The HACL\* / Vale F\* proof discharges the EdDSA correctness axiom
  that our prototype assumes about the Edwards group law + scalarmult
  composition.
* The Vale taint-tracking proof discharges the CT axiom that our
  prototype assumes about gcc's `-O3` on the Edwards group law.
* The leaf is a fixed binary symbol; no compiler dependency beyond
  the trusted assembler (gas/clang-as) to encode the `.S`.

## Relation to the AUCurves Coq-extracted decomposition

The AUCurves OCaml-extracted Jasmin stub list provides a finer
factoring of Ed25519 sign — one stub per primitive (sha512_64,
clamp_64, scalar_reduce, scalar_muladd, ed25519_scalarmult_base,
ed25519_compress, plus the eight region-copy memmove helpers).  At
the verified-front level both factorings denote to the same RFC 8032
sign function; we pick the HACL\* whole-primitive boundary because
HACL\*'s F\* proof is anchored there.  Adopting the AUCurves
decomposition leaf-by-leaf is a finer-grained future variant (Phase B
of #213's wave-2 roadmap), but it does not change the trust shape.
-/

namespace CatCrypt.Crypto.Vale.Ed25519

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage

/-! ## §1. Opaque surface types

Three buffer shapes appear in the Ed25519 leaf C signatures:

* `Ed25519Priv` — 32-byte private seed.
* `Ed25519Pub`  — 32-byte compressed public key.
* `Ed25519Sig`  — 64-byte detached signature `R ‖ S`.
* `Ed25519Msg`  — variable-length message buffer (we treat it as
  opaque at the leaf surface; the verified front passes a pointer-
  plus-length pair through the LowCT extCall ABI).

All four are opaque axiomatic types; the concrete leaves at link
time are the HACL\* C symbols. -/

/-- A 32-byte Ed25519 private seed.  Opaque; concrete leaf is the
    HACL\* Vale-verified `Hacl_Ed25519_sign` consumed buffer. -/
axiom Ed25519Priv : Type
/-- Axiomatic inhabitant. -/
axiom Ed25519Priv.default : Ed25519Priv
noncomputable instance : Inhabited Ed25519Priv :=
  ⟨Ed25519Priv.default⟩

/-- A 32-byte Ed25519 compressed public key. -/
axiom Ed25519Pub : Type
/-- Axiomatic inhabitant. -/
axiom Ed25519Pub.default : Ed25519Pub
noncomputable instance : Inhabited Ed25519Pub :=
  ⟨Ed25519Pub.default⟩

/-- A 64-byte detached Ed25519 signature `R ‖ S`. -/
axiom Ed25519Sig : Type
/-- Axiomatic inhabitant. -/
axiom Ed25519Sig.default : Ed25519Sig
noncomputable instance : Inhabited Ed25519Sig :=
  ⟨Ed25519Sig.default⟩

/-- An Ed25519 message buffer (variable length; opaque at the leaf
    surface). -/
axiom Ed25519Msg : Type
/-- Axiomatic inhabitant. -/
axiom Ed25519Msg.default : Ed25519Msg
noncomputable instance : Inhabited Ed25519Msg :=
  ⟨Ed25519Msg.default⟩

/-! ## §2. Vale-leaf axioms (the trust delta)

The four axioms we add to CatCrypt's axiom budget when we permit
the Vale-verified Ed25519 sign / verify leaves.  Each is sourced
from HACL\* / Vale's upstream F\* proofs against `Spec.Ed25519`. -/

/-- **Denotation axiom (sign)**: the Vale-verified `Hacl_Ed25519_sign`
    leaf computes the RFC 8032 §5.1.6 Ed25519 signature of `msg`
    under `priv`.  Discharged by the F\* functional-correctness proof
    in `Hacl.Ed25519.fst` against `Spec.Ed25519.sign`, composed with
    the Vale proofs on the underlying Curve25519 field arithmetic
    and SHA-512 compression. -/
axiom Vale_Hacl_Ed25519_sign_denote
    (priv : Ed25519Priv) (msg : Ed25519Msg) : Ed25519Sig

/-- **Leakage function (sign)**: the observable trace the
    `Hacl_Ed25519_sign` leaf emits on the given seed and message. -/
axiom Vale_Hacl_Ed25519_sign_leak
    (priv : Ed25519Priv) (msg : Ed25519Msg) : LeafLeak

/-- **Constant-time axiom (sign)**: the leakage trace of the
    `Hacl_Ed25519_sign` leaf is the same at every seed and message.  Both
    buffers carry HACL\*'s secret integer types, and the signing path takes no
    declassification, so no branch or memory index reads either.  The message
    length is a separate public ABI parameter and is not an argument of this
    leaf.  Cited in `ValeCoqAxioms.lean`. -/
axiom Vale_Hacl_Ed25519_sign_CT :
    SecretIndependent (fun q : Ed25519Priv × Ed25519Msg =>
      Vale_Hacl_Ed25519_sign_leak q.1 q.2)

/-- **Denotation axiom (verify)**: the Vale-verified `Hacl_Ed25519_verify`
    leaf returns the RFC 8032 §5.1.7 verification result — `Bool`
    encoded into a single-byte buffer at the C ABI; we model it as
    an `Ed25519Sig`-shaped opaque output (the leaf writes a one-byte
    result via the same SSA tower as the signing-output path; the
    bool is recovered by reading the LSB). -/
axiom Vale_Hacl_Ed25519_verify_denote
    (pk : Ed25519Pub) (msg : Ed25519Msg) (sig : Ed25519Sig) : Ed25519Sig

/-- **Leakage function (verify)**: the observable trace the
    `Hacl_Ed25519_verify` leaf emits on the given public key, message and
    signature. -/
axiom Vale_Hacl_Ed25519_verify_leak
    (pk : Ed25519Pub) (msg : Ed25519Msg) (sig : Ed25519Sig) : LeafLeak

/-- **Variable-time verify**: the leakage trace of the `Hacl_Ed25519_verify`
    leaf varies with its arguments.  The scalar range check and the point
    equality test declassify limbs through `Lib.RawIntTypes` and branch on the
    results, so two argument triples can produce different traces.  All three
    arguments are public, so the branching is licensed by the public-taint
    policy; the leaf must not be applied to secret data.  This is the reject
    side of the same predicate the sign leaf satisfies.  Cited in
    `ValeCoqAxioms.lean`. -/
axiom Vale_Hacl_Ed25519_verify_not_CT :
    ¬ SecretIndependent (fun q : Ed25519Pub × Ed25519Msg × Ed25519Sig =>
      Vale_Hacl_Ed25519_verify_leak q.1 q.2.1 q.2.2)

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the `Vale/Curve25519.lean` and `Vale/SHA512.lean` patterns:
registering both leaves so the verified front accepts the extCalls
as well-formed.

* `Hacl_Ed25519_sign` — arity 2 (priv, msg) → sig.
* `Hacl_Ed25519_verify` — arity 3 (pk, msg, sig) → bool-shaped
  output buffer.

(The C ABI also threads `msg_len` as a separate `uint32_t`; we
encode `msg` as a single opaque buffer at the SSA-tower surface and
let the verified front's extCall ABI carry the length alongside
the pointer, matching the pattern used in `Vale/SHA512.lean`.) -/

/-- Register `Vale_Hacl_Ed25519_sign_denote` → leaf
    `Hacl_Ed25519_sign` (the C symbol name, matching the
    HACL\* `Hacl_Ed25519.c` export). -/
@[rust_cmd_pattern]
def ed25519SignPattern : LowCTPattern where
  name      := "Hacl_Ed25519_sign"
  fnHead    := ``Vale_Hacl_Ed25519_sign_denote
  arity     := 2
  towerType := .TBytes 32   -- 32-byte slot; sig is two of these at the C ABI

/-- Register `Vale_Hacl_Ed25519_verify_denote` → leaf
    `Hacl_Ed25519_verify` (the C symbol name, matching the
    HACL\* `Hacl_Ed25519.c` export). -/
@[rust_cmd_pattern]
def ed25519VerifyPattern : LowCTPattern where
  name      := "Hacl_Ed25519_verify"
  fnHead    := ``Vale_Hacl_Ed25519_verify_denote
  arity     := 3
  towerType := .TBytes 32   -- 32-byte slot; sig is two of these at the C ABI

/-! ## §4. Tower-type abbreviations -/

/-- Tower type of an Ed25519 32-byte buffer (priv / pub / sig-half /
    msg surface) — `TBytes 32`. -/
def ed25519BufTowerType : TowerType := .TBytes 32

/-! ## §5. `LeafSig` entries for the Vale leaves

Both Vale leaves are **non-aliasing** at the SSA level: signature,
private/public key, and message buffers are distinct in the HACL\*
C signatures (`Hacl_Ed25519_sign(sig, priv, len, msg)` and
`Hacl_Ed25519_verify(pk, len, msg, sig)`).  We declare
`destAliasOk := []` (the conservative default). -/

/-- Per-leaf signature for `Hacl_Ed25519_sign`: no aliasing
    permitted (signature, private key, and message buffer all
    distinct in HACL\*'s C signature). -/
def ed25519SignLeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "Hacl_Ed25519_sign"
  destAliasOk := []

/-- Per-leaf signature for `Hacl_Ed25519_verify`: no aliasing
    permitted (public key, message, signature, and result buffer
    all distinct in HACL\*'s C signature). -/
def ed25519VerifyLeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "Hacl_Ed25519_verify"
  destAliasOk := []

/-! ## §6. Pure-Lean wrappers — the specs

Pure-Lean wrappers for the Ed25519 sign and verify operations,
serving as the front-end input to the reflection pipeline.  Each
body is a single Vale-leaf call. -/

/-- One Ed25519 sign invocation: produce the 64-byte detached
    signature of `msg` under the 32-byte `priv` seed. -/
noncomputable def valeEd25519SignLean
    (priv : Ed25519Priv) (msg : Ed25519Msg) : Ed25519Sig :=
  Vale_Hacl_Ed25519_sign_denote priv msg

/-- One Ed25519 verify invocation: return the verification result
    (encoded into the `Ed25519Sig`-shaped output slot per §2). -/
noncomputable def valeEd25519VerifyLean
    (pk : Ed25519Pub) (msg : Ed25519Msg) (sig : Ed25519Sig) : Ed25519Sig :=
  Vale_Hacl_Ed25519_verify_denote pk msg sig

/-! ## §7. Hand-built `LowCT` bodies (front-end input)

Following the `VaesReflect.vaesEnc2WayBody` / `Vale/Curve25519.lean`
pattern: the front-end `reifyLowCT%` macro reads `knownOps` only,
so we hand-build the single-`RCall` bodies the reifier would
produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `valeEd25519SignLean`. Shape:
    `RSeq RSkip (RCall "Hacl_Ed25519_sign"
                       __result [priv, msg])`. -/
def valeEd25519SignBody : LowCT :=
  let priv_l   := loc "priv" ed25519BufTowerType
  let msg_l    := loc "msg"  ed25519BufTowerType
  let result_l := loc "__result" ed25519BufTowerType
  .RSeq .RSkip
    (.RCall "Hacl_Ed25519_sign"
            result_l [priv_l, msg_l])

/-- The `LowCT` body for `valeEd25519VerifyLean`. Shape:
    `RSeq RSkip (RCall "Hacl_Ed25519_verify"
                       __result [pk, msg, sig])`. -/
def valeEd25519VerifyBody : LowCT :=
  let pk_l     := loc "pk"  ed25519BufTowerType
  let msg_l    := loc "msg" ed25519BufTowerType
  let sig_l    := loc "sig" ed25519BufTowerType
  let result_l := loc "__result" ed25519BufTowerType
  .RSeq .RSkip
    (.RCall "Hacl_Ed25519_verify"
            result_l [pk_l, msg_l, sig_l])

/-- `ReifiedFunc` bundle for the Vale Ed25519 sign leaf. -/
def valeEd25519SignReified : ReifiedFunc :=
  { args    := [("priv", ed25519BufTowerType),
                ("msg",  ed25519BufTowerType)]
    body    := valeEd25519SignBody
    retName := "__result" }

/-- `ReifiedFunc` bundle for the Vale Ed25519 verify leaf. -/
def valeEd25519VerifyReified : ReifiedFunc :=
  { args    := [("pk",  ed25519BufTowerType),
                ("msg", ed25519BufTowerType),
                ("sig", ed25519BufTowerType)]
    body    := valeEd25519VerifyBody
    retName := "__result" }

/-! ## §8. Inspection -/

#eval valeEd25519SignReified.args.map Prod.fst
  -- [priv, msg]
#eval valeEd25519SignReified.args.length        -- 2
#eval valeEd25519SignReified.retName            -- __result

#eval valeEd25519VerifyReified.args.map Prod.fst
  -- [pk, msg, sig]
#eval valeEd25519VerifyReified.args.length      -- 3
#eval valeEd25519VerifyReified.retName          -- __result

end CatCrypt.Crypto.Vale.Ed25519
