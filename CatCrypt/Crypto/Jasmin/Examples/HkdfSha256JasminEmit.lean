/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.HkdfSha256Jasmin

/-!
# Emit driver for HKDF-SHA-256

`main` runs `HkdfSha256Jasmin.runEmit`, which reads the HMAC-SHA-256 bundle from
`/tmp/hmac_sha256_jasmin.rs`, appends the HKDF functions, and writes the result to
`/tmp/hkdf_sha256_jasmin.rs`.
-/

@[expose] public section
/-- Driver script: `lake env lean --run …/HkdfSha256JasminEmit.lean`. -/
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.HkdfSha256Jasmin.runEmit
