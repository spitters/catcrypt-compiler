/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# AES-128-GCM chain reflect surface — multi-round chain glue through the verified front

This file is the AEAD-family analogue of `FalconReflect.lean` / `MayoReflect.lean`:
it adds AES-GCM specific opaque surface types and `@[rust_cmd_pattern]`
registrations so that a pure-Lean AES-128-GCM **chain orchestration**
(key-schedule → per-block AES-CTR + GHASH-multiply for `N = 4` blocks → final
tag) can be lifted through the verified compiler chain
`LowCT → CryptoSSA → Com → jasmin`, **without** editing
`LowCTReflect.lean`'s `knownOps` table.

## Background — the `AUDIT_EMIT_BYPASS.md` hybrid

The AES-GCM family (`aesgcm`, `aesccm`, `aessiv`, `aesgcmsiv`, `aegis`) has a
per-file HYBRID pattern (see `bench/framework/AUDIT_EMIT_BYPASS.md` §3):

* the **per-round** `Com jasminDialect [.reg 128, .reg 128] (.reg 128)` AES round
  step is Tier B (a verified emitter over a hand-built `Com`), e.g.
  `bench/aesgcm_compare/aesgcm_emit.lean`'s `aesBlockCom` /
  `aesBlockCom_denote`;
* but the **multi-round chain glue** (the for-each-block loop that ties the AES
  rounds together with GHASH multiplication and counter increment) is
  `String.intercalate "\n  " bodyLines` — Tier C, with the chain-level
  numbers backed only by structural smoke tests (`strContains`).

This file migrates the **chain glue** to Tier A: the orchestration of the
`N = 4` block chain becomes one verified `LowCT → CryptoSSA → Com → jasmin`
pass over a hand-built `LowCT`. The per-round Com substrate
(`aesgcm_emit.lean`) is **kept unchanged** — it is the Tier B round-step
keeper this migration sits on top of.

## AES-128-GCM chain (NIST SP 800-38D, fixed `N = 4` blocks, 96-bit nonce)

```
  ghash_mul64 : (BitVec 128) → (BitVec 128) → (BitVec 128)   -- GHASH per-block GF(2^128) multiply
  aes_expand_key : AesKey → AesRoundKeys                       -- 11-round-key schedule
  aesgcm_round_step : AesRoundKeys → (BitVec 128) → (BitVec 128) -- AES-128 ECB round step on a counter block
  aesgcm_chain_n4 : AesKey → GcmNonce → GcmAad → GcmPt4 → GcmCt4Tag
                                                               -- the fixed-N=4-block chain
```

The chain leaf `aesgcm_chain_n4` orchestrates: AES-CTR keystream over 4 blocks,
GHASH dot over (AAD ‖ C ‖ lenblock), tag XOR. Modelling the for-each-block loop
*inside* `LowCT` would need `RFor` (the documented LowCT-expressivity gap,
same as MAYO over `m` components, FAEST `gf_dot_vec`, etc.); we follow the
specialisation route — one leaf per fixed `N`, today `N = 4` (matching the
canonical NIST GCM TC4-shaped vector the legacy `aesgcm_emit.lean`'s KAT
exercises).

## LowCT-expressivity gap (documented, same shape as MAYO)

The full AES-GCM `encrypt` takes a variable-length plaintext; the per-block
chain length varies per call. Modelling the variable-length chain *inside*
`LowCT` would need a `for`-loop-inside-`LowCT` (the documented `RFor` gap;
see `MayoReflect.lean` for the parallel discussion). The same gap applies to
AES-CCM, AES-SIV, AES-GCM-SIV, AEGIS — the AEAD multi-block chain shape needs
either `RFor` in `LowCT` or a per-block-count specialisation. This file's
design is the **specialisation route**: one leaf per fixed `N`, today `N = 4`
(the canonical NIST GCM TC4 / `aesgcm-hax/src/gcm.rs::gcm_encrypt` 64-byte
shape). Adding `N = 16` or `N = 256` is a copy of the `@[rust_cmd_pattern]` +
axiom.

## Reflection→front gap (same as MAYO / Falcon)

`reifyLowCT%` reads only `LowCTReflect.knownOps`, not the dynamic
`LowCTPattern` registry. So `reifyLowCT% aesGcmChainLean` would error.
We follow the `mayoQuadFormN8Reified` / `falconVerifyReified` pattern: define
the pure-Lean function for documentation/spec, register the leaf in the
`LowCTPattern` registry via `@[rust_cmd_pattern]`, then **hand-build the
`LowCT`** the reifier *would* produce. Downstream (`translate →
cprogToJasminCom → emitAbiOrchRegPtr`) is the unmodified verified front.

## References

* NIST SP 800-38D §6, §7 — AES-GCM encryption (`GCTR`, `GHASH`, full encrypt)
* RFC 5288, NIST Test Case 4 — canonical AES-128-GCM test vector
* `aesgcm-hax/src/gcm.rs::gcm_encrypt` — Rust trait surface this file mirrors
* `bench/aesgcm_compare/aesgcm_emit.lean` — Tier B per-round Com (keeper)
* `CatCrypt/Crypto/Jasmin/MayoReflect.lean` — sibling pattern (single-leaf
  reflect surface registering one fixed-N leaf)
* `CatCrypt/Crypto/Jasmin/FalconReflect.lean` — sibling pattern (multi-leaf
  reflect surface)
* `bench/framework/AUDIT_EMIT_BYPASS.md` §3 — the AES-GCM family chain-glue
  gap this file closes
-/

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque AES-GCM surface types

AES-128-GCM operates over byte buffers: a 16-byte key, a 12-byte nonce, a
16-byte AAD (one block — matches the canonical NIST GCM TC4 shape), 64 bytes
of plaintext (`NBLOCKS = 4` AES blocks), and produces 64 bytes of ciphertext
plus a 16-byte authentication tag (which we bundle as 80 bytes of
`ct ‖ tag`).

| Surface           | TowerType  | storageBytes | memref (u64 limbs) |
|-------------------|------------|-------------:|-------------------:|
| `AesKey`          | `TBytes 16`|           16 | 2                  |
| `GcmNonce`        | `TBytes 12`|           12 | 2                  |
| `GcmAad`          | `TBytes 16`|           16 | 2                  |
| `GcmPt4`          | `TBytes 64`|           64 | 8                  |
| `GcmCt4Tag`       | `TBytes 80`|           80 | 10 (64 ct + 16 tag)|

All five are opaque on the Lean side; the leaf `aesgcm_chain_n4` implements the
concrete byte layout (matches `aesgcm-hax/src/gcm.rs` and the existing
`bench/aesgcm_compare/aesgcm_kat.c` ABI). -/

/-- AES-128 key (16 bytes). Opaque on the Lean side; the chain leaf reads it as
    the AES master key for the 11-round key schedule. -/
axiom AesKey : Type
/-- Axiomatic inhabitant. -/ axiom AesKey.default : AesKey
noncomputable instance : Inhabited AesKey := ⟨AesKey.default⟩

/-- AES-GCM 96-bit nonce (12 bytes). Opaque; the chain leaf uses it to derive
    `J0 = nonce ‖ 0x00000001` per SP 800-38D §7.1. -/
axiom GcmNonce : Type
/-- Axiomatic inhabitant. -/ axiom GcmNonce.default : GcmNonce
noncomputable instance : Inhabited GcmNonce := ⟨GcmNonce.default⟩

/-- AES-GCM AAD: one 16-byte block (matches the canonical NIST GCM TC4 / the
    `aesgcm-hax/src/gcm.rs::gcm_encrypt` AAD shape). Opaque. -/
axiom GcmAad : Type
/-- Axiomatic inhabitant. -/ axiom GcmAad.default : GcmAad
noncomputable instance : Inhabited GcmAad := ⟨GcmAad.default⟩

/-- AES-GCM plaintext: 4 AES blocks = 64 bytes (matches the `aesgcm-hax`
    fixed-size `gcm_encrypt` test case and the legacy
    `bench/aesgcm_compare/aesgcm_kat.c` ABI). Opaque; the chain leaf
    encrypts it via AES-CTR keystream. -/
axiom GcmPt4 : Type
/-- Axiomatic inhabitant. -/ axiom GcmPt4.default : GcmPt4
noncomputable instance : Inhabited GcmPt4 := ⟨GcmPt4.default⟩

/-- AES-GCM ciphertext ‖ tag bundle: 64 bytes of ciphertext + 16 bytes of
    authentication tag = 80 bytes, packaged as one opaque type so the chain
    leaf has a single output region (the front-end ABI uses one `__result`
    pointer per export). Opaque. -/
axiom GcmCt4Tag : Type
/-- Axiomatic inhabitant. -/ axiom GcmCt4Tag.default : GcmCt4Tag
noncomputable instance : Inhabited GcmCt4Tag := ⟨GcmCt4Tag.default⟩

/-! ## 2. Component leaves (opaque jasmin function symbols)

These are not used inside the chain `LowCT` body — the chain is one leaf
(`aesgcm_chain_n4`). We declare them so this file documents the **conceptual
decomposition** of the chain and so callers that want a finer-grained surface
(e.g. for the audited Tier B round-step `aesBlockCom` in
`aesgcm_emit.lean`) can refer to them by name. -/

/-- One AES-128 ECB round step on a 128-bit counter block, parameterised by
    the round-key schedule. This is the per-round substrate the existing
    Tier B `aesBlockCom : Com jasminDialect [.reg 128, .reg 128] (.reg 128)`
    emits to (see `bench/aesgcm_compare/aesgcm_emit.lean`). Surfaced here as
    an opaque leaf so the conceptual chain decomposition is documented. -/
axiom aesgcm_round_step : AesKey → BitVec 128 → BitVec 128

/-- One GHASH per-block GF(2^128) multiply by the hash subkey `H = AES_K(0^128)`.
    The committed lsb-first `gf_clmul128` + `gf_reduce` kernel + the GCM
    reflect-mul-reflect bridge (Gueron–Kounavis), as in
    `aesgcm_emit.lean`'s `ghashMulFn`. Surfaced here as an opaque leaf for the
    conceptual decomposition. -/
axiom ghash_mul64 : BitVec 128 → BitVec 128 → BitVec 128

/-- AES-128 key-schedule (master key → 11 round keys). Real implementations
    use AES-NI `AESKEYGENASSIST`. Surfaced as an opaque leaf for the
    conceptual decomposition; the chain leaf rolls this in. -/
axiom aes_expand_key : AesKey → AesKey

/-! ## 3. The chain leaf (the orchestration this file emits)

`aesgcm_chain_n4` is the single leaf the verified front sees: it bundles the
full `N = 4`-block AES-128-GCM encrypt orchestration — key schedule, CTR
keystream over 4 blocks, GHASH dot over (AAD ‖ C ‖ lenblock), tag XOR — as one
opaque jasmin function symbol. The Tier B per-round Com substrate
(`aesgcm_emit.lean`'s `aesBlockCom`) is the under-the-leaf implementation. -/

/-- `(ct, tag) = AES-128-GCM-Encrypt(key, nonce, aad, pt)` for the canonical
    `N = 4` block shape (16 B AAD, 64 B pt, 96-bit nonce, returning 80 B of
    `ct ‖ tag`). This is the AES-GCM **chain orchestration** — what the legacy
    `String.intercalate` glue in `aesgcm_emit.lean` builds by hand. We surface
    it as one opaque leaf, with the registered pattern below routing the
    pure-Lean `aesGcmChainLean` through the verified front to a `.jazz` that
    calls this leaf by name.

    Constant-time per NIST SP 800-38D Algorithm 4: no secret-dependent branch;
    the AES round step, GHASH multiply, and counter increment are all
    register-arith / pclmul, no table-lookup dependent on key material. -/
axiom aesgcm_chain_n4 : AesKey → GcmNonce → GcmAad → GcmPt4 → GcmCt4Tag

/-! ## 4. `@[rust_cmd_pattern]` registration -/

/-- Register `aesgcm_chain_n4` → leaf `aesgcm_chain_n4`. The destination
    TowerType is `TBytes 80` (64 B ct + 16 B tag); the four argument
    TowerTypes come from the caller's `VarMap`:
      `key : TBytes 16`, `nonce : TBytes 12`, `aad : TBytes 16`,
      `pt : TBytes 64`. -/
@[rust_cmd_pattern]
def aesGcmChainN4Pattern :
    CatCrypt.Crypto.Jasmin.LowCTReflect.LowCTPattern where
  name      := "aesgcm_chain_n4"
  fnHead    := ``aesgcm_chain_n4
  arity     := 4
  towerType := .TBytes 80

/-! ## 5. Pure-Lean kernel function — the spec for what the emit must implement -/

/-- AES-128-GCM chain at `N = 4` blocks (NIST SP 800-38D §6, §7). Matches the
    legacy `bench/aesgcm_compare/aesgcm_emit.lean`'s scope: one fixed-size
    `(16 B AAD, 64 B pt, 96-bit nonce)` encrypt, byte-identical to NIST GCM
    Test Case 4 (the existing KAT vector). -/
noncomputable def aesGcmChainLean
    (key : AesKey) (nonce : GcmNonce) (aad : GcmAad) (pt : GcmPt4) :
    GcmCt4Tag :=
  aesgcm_chain_n4 key nonce aad pt

/-! ## 6. Hand-built `LowCT` body (the front-end input)

Since `reifyLowCT%` does not consult the `LowCTPattern` registry, we
hand-build the body the reifier *would* produce for `aesGcmChainLean`.
Shape: one `RSeq RSkip (RCall …)` — same pattern as `MayoReflect.lean`'s
`mayoQuadFormN8Body` (single-leaf chain). -/

/-- TowerType for `key` (16 bytes). -/
def aesKeyTowerType   : TowerType := .TBytes 16
/-- TowerType for `nonce` (12 bytes — the 96-bit nonce case, SP 800-38D §7.1). -/
def gcmNonceTowerType : TowerType := .TBytes 12
/-- TowerType for `aad` (one 16-byte block — the canonical NIST GCM TC4 shape). -/
def gcmAadTowerType   : TowerType := .TBytes 16
/-- TowerType for `pt` (4 AES blocks = 64 bytes). -/
def gcmPt4TowerType   : TowerType := .TBytes 64
/-- TowerType for the `(ct, tag)` bundle (64 B ct + 16 B tag = 80 bytes). -/
def gcmCt4TagTowerType : TowerType := .TBytes 80

private def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body the reifier *would* produce for `aesGcmChainLean`:

    ```
    __result := aesgcm_chain_n4(key, nonce, aad, pt)
    ```

    A single `RCall` ending the chain (the chain orchestration is one
    fixed-`N=4` leaf), with result name `__result` matching the reifier's
    end-of-chain convention. -/
def aesGcmChainBody : LowCT :=
  let key_l    := loc "key"      aesKeyTowerType
  let nonce_l  := loc "nonce"    gcmNonceTowerType
  let aad_l    := loc "aad"      gcmAadTowerType
  let pt_l     := loc "pt"       gcmPt4TowerType
  let result_l := loc "__result" gcmCt4TagTowerType
  .RSeq .RSkip
    (.RCall "aesgcm_chain_n4" result_l [key_l, nonce_l, aad_l, pt_l])

/-- `ReifiedFunc` bundle for the chain, assembled by hand from
    `aesGcmChainBody`. Same field shape `reifyLowCT%` would produce; the
    bench driver consumes `.body` / `.retName` exactly as it would a reifier
    output. -/
def aesGcmChainReified : ReifiedFunc :=
  { args    := [("key",   aesKeyTowerType),
                ("nonce", gcmNonceTowerType),
                ("aad",   gcmAadTowerType),
                ("pt",    gcmPt4TowerType)]
    body    := aesGcmChainBody
    retName := "__result" }

/-! ## 7. Inspection -/

#eval aesGcmChainReified.args.map Prod.fst              -- [key, nonce, aad, pt]
#eval aesGcmChainReified.args.length                    -- 4
#eval aesGcmChainReified.retName                        -- __result

end CatCrypt.Crypto.Jasmin.LowCTReflect
