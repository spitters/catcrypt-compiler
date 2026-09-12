/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Crypto.Jasmin.LeafSig
public import CatCrypt.Crypto.Jasmin.LeafSig
public meta import CatCrypt.Crypto.Vale.LeafLeakage
public import CatCrypt.Crypto.Vale.LeafLeakage
public meta import CatCrypt.Crypto.Util.Aes128Verified
public import CatCrypt.Crypto.Util.Aes128Verified
public meta import CatCrypt.Crypto.Util.Gf128Verified
public import CatCrypt.Crypto.Util.Gf128Verified

@[expose] public section

set_option autoImplicit false

/-!
# Vale-verified GHASH-CLMUL leaf (`aes128_keyhash_init`)

This module declares the Vale-verified HACL\* `aes128_keyhash_init`
implementation — the GHASH H-power-table precomputation driven by
PCLMULQDQ in `hacl/c/vale/src/aesgcm-x86_64-linux.S` — as an opaque
verified-CT leaf for CatCrypt's verified front, following the established
extCall pattern (Jasmin.LowCT `RCall`).

This is the GHASH-CLMUL entry of the Vale-leaf pattern. The companion
`Vale/AESGCM.lean` covers the whole AEAD; this file isolates the GHASH
primitive (the PCLMULQDQ-driven GF(2^128) multiplications) as its own
leaf, so the verified front can compose it with any AES-CTR keystream
(including non-Vale ones) and so the residual on ChaCha20-Poly1305 +
AES-GCM AEAD compositions can be closed by routing only the GHASH part
through Vale.

## Architectural claim (the composition)

```
CatCrypt(glue) + Vale(leaf)
    via the extCall denotation at the Veir/Jasmin extCall boundary
    -> verified-CT pipeline
```

CatCrypt's verified front discharges the orchestration; the leaf's
denotation matches the Vale F\* proof (cited below); CT is inherited
from Vale's taint-tracking proof on the implementation side.

## The HACL\* / Vale provenance

* **Linker symbol**: `aes128_keyhash_init`, declared `.global` in
  `aesgcm-x86_64-linux.S` (libcrux/HACL* Vale).
  Consumed by `EverCrypt_AEAD.c`'s `expand_aes128_gcm` and by the
  Vale-verified AES-GCM driver as the GHASH-subkey precomputation.
* **Function**: computes the GHASH H-power table from an AES-128
  expanded-round-keys schedule (the 176-byte `keys_b`). Specifically,
  it derives `H = AES_K(0^128)` by running one AES-128 block-encrypt
  on the all-zero block under the expanded key, then computes the
  precomputed powers `H, H^2, H^3, H^4` in the 128-byte table
  `hkeys_b`. The GF(2^128) squarings use PCLMULQDQ for the carry-less
  multiplies + a fixed shift+XOR reduction by `g(x) = x^128 + x^7 +
  x^2 + x + 1`.
* **F\* / Vale source**: `hacl-star/vale/code/crypto/aes/x64/`,
  files `Vale.AES.X64.AESCTRplain.fst` (`keyhash_init` driver) and
  `Vale.AES.GHash_BE.fst` (the GHASH H-power-table spec). The
  functional spec is `Vale.AES.GHash_BE.ghash_incremental_def`
  matching NIST SP 800-38D §6.4 GHASH definition.
* **Vale PCLMULQDQ correctness**: `Vale.AES.X64.GHash.fst` proves
  the per-PCLMUL `vinstr_VPCLMULQDQ` matches the GF(2^128) multiply
  spec; the H-power-table compute is the four-call schoolbook
  composition of this primitive (one for `H * H`, one for `H * H^2`,
  one for `H * H^3`, with shared LL/HL/LH/HH structure per multiply).
* **NIST CAVP**: HACL\*'s GCM tests (Test Case 1, 3, 4 from the GCM
  spec appendix) all flow through `aes128_keyhash_init` — the H-power
  table they produce is the same one the existing CatCrypt
  `bench/ghash_vpclmul_compare/ghash_conform.c` cross-checks against
  `_mm_clmulepi64_si128` reference.

## Leaf C signature

```c
extern void aes128_keyhash_init(uint8_t *keys_b, uint8_t *hkeys_b);
```

That is: `aes128_keyhash_init(expanded_round_keys, out_hkeys_table)`
computes the 128-byte H-power table `[H, H^2, H^3, H^4]` (each 16
bytes, GCM bit-reflected) from the 176-byte AES-128 expanded-round-
keys schedule. Both buffers must be 16-byte-aligned.

## Trust delta (what we trust ABOVE CatCrypt's normal axiom set)

The denotation is an owned composition of computable proven specs, not
an axiom: `Vale_aes128_keyhash_init_denote` computes the H-power table
`[H, H^2, H^3, H^4]` with `H = Util.Aes128.encrypt K 0^128` and the
powers `Util.Gf128.mul` (the NIST SP 800-38D §6.3 reduced GF(2^128)
multiply modulo `g(x) = x^128 + x^7 + x^2 + x + 1`), the same block
convention `AESGCM.AesGcmVerified` uses. By adopting this leaf we
additionally trust:

1. **Vale_aes128_keyhash_init_CT**: the leaf is constant-time in
   the input `keys_b` (the AES round-keys, which are derived from
   the secret AES key). Sourced from Vale's taint-tracking proof on
   the PCLMULQDQ + AES-NI register-arith body (no table lookups,
   no secret-dependent branches or memory accesses).

The trust delta is **strictly smaller** than the all-our-emit path
when the alternative is a hand-emitted PCLMULQDQ + reduction body
we have not proved against `Vale.AES.GHash_BE.ghash_incremental_def`.
For GHASH specifically, the existing CatCrypt VPClmul demonstrator
(`bench/ghash_vpclmul_compare/ghash_vpclmul_emit.lean`) emits the
four-call schoolbook PCLMUL chain with a placeholder reduction; the
Vale leaf replaces this with a fully-verified end-to-end H-power
table compute that includes the full reduction sequence.

## Scope

This leaf is the **GHASH key-schedule precomputation** — the
PCLMULQDQ-driven step that produces the H-power table. The per-block
GHASH update during AEAD encryption/decryption is fused into
`gcm128_encrypt_opt` in `aesgcm-x86_64-linux.S` and is covered by
`Vale/AESGCM.lean`'s `Vale_AES128_GCM_encrypt_denote` axiom. The
two leaves together cover the full GHASH-CLMUL surface that
`hacl/c/vale/src/aesgcm-x86_64-linux.S` exposes.
-/

namespace CatCrypt.Crypto.Vale.GHASH

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage
open CatCrypt.Util

/-! ## §1. Surface types

Two operand types for the canonical `aes128_keyhash_init` call: the
176-byte AES-128 expanded-round-keys schedule (input), and the H-power
table `[H, H^2, H^3, H^4]` (output).

Both are owned computable types: the input is the byte buffer the Vale
leaf reads as `uint8_t *keys_b`; the output is the four GF(2^128)
elements the leaf writes. -/

/-- A Vale-GHASH AES-128 expanded-round-keys buffer: 176 bytes (11 ×
    16-byte round keys). The Vale leaf reads it as a `uint8_t *keys_b`
    argument. Its first 16 bytes are the AES-128 key; the remaining
    bytes are that key's `aes128_key_expansion`. -/
abbrev ValeGhashAesKeys : Type := Fin 176 → UInt8

/-- A Vale-GHASH H-power table: the four 16-byte GF(2^128) elements
    `[H, H^2, H^3, H^4]` the Vale leaf writes to `uint8_t *hkeys_b`
    (each a `BitVec 128` in the `Util.Aes128` / `Util.Gf128` block
    convention that `AESGCM.AesGcmVerified` uses). -/
abbrev ValeGhashHkeyTable : Type :=
  Aes128.Block × Aes128.Block × Aes128.Block × Aes128.Block

/-! ## §2. Owned denotation and the CT trust handle

The leaf's denotation is an owned composition of computable proven
specs (`Util.Aes128.encrypt` for `H`, `Util.Gf128.mul` for the powers).
The single remaining trust handle is the constant-time property, sourced
from Vale's upstream F\* / taint-tracking proof (cited in the module
docstring). -/

/-- The H-power-table denotation of `aes128_keyhash_init`: from a
    176-byte AES-128 expanded round-keys schedule, take the embedded
    key (first 16 bytes), set `H = AES_K(0^128)`, and return the four
    GF(2^128) powers `[H, H^2, H^3, H^4]` taken modulo
    `g(x) = x^128 + x^7 + x^2 + x + 1` (NIST SP 800-38D §6.3).

    `H` is `Util.Aes128.encrypt` on the all-zero block; the powers are
    `Util.Gf128.mul` — the same owned block convention `AesGcmVerified`
    uses for the GHASH subkey and its multiply. Faithful to the leaf
    under the C precondition that `keys_b` is an AES-128 key expansion:
    re-expanding its first 16 bytes reproduces `keys_b`, so `H` matches
    the value the leaf derives from the schedule's round keys. -/
noncomputable def Vale_aes128_keyhash_init_denote
    (keys : ValeGhashAesKeys) : ValeGhashHkeyTable :=
  let keyBytes : Fin 16 → UInt8 := fun i => keys ⟨i.val, by have := i.isLt; omega⟩
  let H  : Aes128.Block := Aes128.encrypt (Aes128.fromBytes keyBytes) Aes128.zeroBlock
  let H2 : Aes128.Block := Gf128.mul H H
  let H3 : Aes128.Block := Gf128.mul H2 H
  let H4 : Aes128.Block := Gf128.mul H3 H
  (H, H2, H3, H4)

/-- **Leakage function**: the observable trace the Vale-verified
    `aes128_keyhash_init` leaf emits on the expanded round-key
    schedule `keys`. -/
axiom Vale_aes128_keyhash_init_leak (keys : ValeGhashAesKeys) : LeafLeak

/-- **Constant-time axiom**: the leakage trace of the Vale-verified
    `aes128_keyhash_init` leaf is the same at every expanded round-key
    schedule `keys`. The body is PCLMULQDQ and AES-NI register arithmetic with
    no table lookup and no key-dependent branch, and the schedule buffer
    carries `Secret` taint in the Vale interop signature. Cited in
    `ValeCoqAxioms.lean`. -/
axiom Vale_aes128_keyhash_init_CT :
    SecretIndependent Vale_aes128_keyhash_init_leak

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the `valeChaCha20Vec256Pattern` / `valeAesGcmPattern`
template: the leaf returns a `TBytes 128` (the H-power table) and
takes one argument (the 176-byte expanded-round-keys schedule).

For the ABI, both are surfaced as `TBytes` regions. The verified
front's `memref`-encoding gives `TBytes 176 → memref 22` (22 × 8 B
limbs = 176 B) for input and `TBytes 128 → memref 16` for output.
-/

/-- TowerType for `keys` (176 B AES-128 expanded-round-keys schedule). -/
def valeKeysTowerType : TowerType := .TBytes 176

/-- TowerType for the output H-power table (128 B = 4 × 16 B). -/
def valeHkeyTowerType : TowerType := .TBytes 128

/-- Register `Vale_aes128_keyhash_init_denote` → leaf
    `aes128_keyhash_init` (the C/asm symbol that the linker resolves
    against `hacl/c/vale/src/aesgcm-x86_64-linux.S`). -/
@[rust_cmd_pattern]
def valeGhashKeyhashInitPattern : LowCTPattern where
  name      := "aes128_keyhash_init"
  fnHead    := ``Vale_aes128_keyhash_init_denote
  arity     := 1
  towerType := .TBytes 128

/-! ## §4. `LeafSig` entry for the Vale leaf

The Vale leaf is **non-aliasing** at the SSA level: `keys_b` and
`hkeys_b` are distinct buffers in `aes128_keyhash_init`'s C signature.
We declare `destAliasOk := []` (the conservative default) — the
borrow checker correctly forbids aliased calls. -/

/-- Per-leaf signature for `aes128_keyhash_init`: no aliasing
    permitted (input `keys_b` and output `hkeys_b` are distinct in
    the Vale asm's C signature). -/
def valeGhashLeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "aes128_keyhash_init"
  destAliasOk := []

/-! ## §5. Pure-Lean wrapper — the spec

A pure-Lean wrapper for the Vale-verified GHASH key-schedule
precomputation, serving as the front-end input to the reflection
pipeline. The body is the single Vale-leaf call. -/

/-- One Vale-verified `aes128_keyhash_init` invocation: produce the
    GHASH H-power table `[H, H^2, H^3, H^4]` from an AES-128 expanded
    round-keys schedule. -/
noncomputable def valeGhashKeyhashInitLean
    (keys : ValeGhashAesKeys) : ValeGhashHkeyTable :=
  Vale_aes128_keyhash_init_denote keys

/-! ## §6. Hand-built `LowCT` body (front-end input)

Following the `valeChaCha20Vec256Body` / `valeAesGcmBody` pattern: the
front-end `reifyLowCT%` macro reads `knownOps` only, so we hand-build
the single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `valeGhashKeyhashInitLean`. Shape:
    `RSeq RSkip (RCall "aes128_keyhash_init" __result [keys])`. -/
def valeGhashKeyhashInitBody : LowCT :=
  let keys_l   := loc "keys"     valeKeysTowerType
  let result_l := loc "__result" valeHkeyTowerType
  .RSeq .RSkip
    (.RCall "aes128_keyhash_init" result_l [keys_l])

/-- `ReifiedFunc` bundle for the Vale GHASH H-power-table leaf. -/
def valeGhashKeyhashInitReified : ReifiedFunc :=
  { args    := [("keys", valeKeysTowerType)]
    body    := valeGhashKeyhashInitBody
    retName := "__result" }

/-! ## §7. Inspection -/

#eval valeGhashKeyhashInitReified.args.map Prod.fst
  -- [keys]
#eval valeGhashKeyhashInitReified.args.length     -- 1
#eval valeGhashKeyhashInitReified.retName         -- __result

end CatCrypt.Crypto.Vale.GHASH
