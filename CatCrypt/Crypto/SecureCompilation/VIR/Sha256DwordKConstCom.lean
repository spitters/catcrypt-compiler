/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import CatCrypt.Crypto.Primitives.SHA256

/-!
# The SHA-256 round-constant tie, model-free (`Com`/`JasminDialect` successor)

`X86Backend/Sha256DwordScheduleRealization.lean` ties the 64 dword
round-constants `kConstD` to the abstract FIPS-180-4 constants
`Primitives.SHA256.kConst` via `kConstD_eq_abstract`. That bespoke statement
lives in the `Avx512DwordModel` tower (it imports
`Sha256DwordRoundRealization`, which transitively pulls the model in),
so deleting `Avx512DwordModel` would take the constant tie with it.

This module reproduces the tie **model-free**: the 64 constants are a fixed
`Vector (BitVec 32) 64` table (the dword lane width), and the tie holds by
`native_decide` over `Fin 64` — exactly the bespoke proof, but standing on
nothing but `Primitives.SHA256` and the model-free `JasminDialect` (which
imports only `VIR.Core`). The `BitVec 32` lane width is the dword
width carried by `JasminDialect`'s dword ops; nothing here depends on the
`ZState32` machine.

## What is delivered (equal-strength successor of `kConstD_eq_abstract`)

| result | content | strength |
|--------|---------|----------|
| `kConstDCom` | the 64 `BitVec 32` round constants (FIPS 180-4 §4.2.2) | — |
| `kConstDComAt` | the `t`-th constant (`0` out of range, matching `kConst`) | — |
| `kConstDCom_eq_abstract` | `kConstDComAt t = (kConst t).toBitVec`, all `t : Fin 64` | **= bespoke** |

The constants are the algorithm's **defining values** (the first 32 bits of the
fractional parts of the cube roots of the first 64 primes), not test vectors,
so `native_decide` over the 64 concrete indices is the canonical witness.

## References
* FIPS 180-4 — Secure Hash Standard (§4.2.2 — the round constants `K`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordKConstCom

open CatCrypt.Crypto.Primitives.SHA256 (kConst)

/-! ## The 64 concrete SHA-256 round constants `K[0..63]` (FIPS 180-4 §4.2.2)

Carried at `BitVec 32` (the dword lane width of `JasminDialect`'s dword ops),
verbatim from the bespoke `kConstD`, and proved equal to the sealed abstract
`Primitives.SHA256.kConst`. -/

/-- The 64 SHA-256 round constants `K[0..63]` at `BitVec 32` (FIPS-180-4 §4.2.2). -/
def kConstDCom : Vector (BitVec 32) 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Look up the `t`-th dword round constant (`0` out of range, matching `kConst`). -/
def kConstDComAt (t : Nat) : BitVec 32 := kConstDCom.toArray.getD t 0

/-- **The dword round constants ARE the abstract `kConst` (model-free).** For every
    index `t`, the `BitVec 32` constant `kConstDComAt t` equals the bit-vector of
    the abstract `Primitives.SHA256.kConst t` — the FIPS-180-4 §4.2.2 round
    constants at the dword lane width. The equal-strength successor of
    `Sha256DwordScheduleRealization.kConstD_eq_abstract`, proved the same way
    (`native_decide` over all 64 indices — the constants are the algorithm's
    defining values), but standing only on `Primitives.SHA256` and the model-free
    `JasminDialect`. -/
theorem kConstDCom_eq_abstract (t : Fin 64) :
    kConstDComAt t.val = (kConst t.val).toBitVec := by
  revert t; native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordKConstCom
