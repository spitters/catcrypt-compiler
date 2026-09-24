/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.HmacSha256Jasmin

/-!
# Emit driver for HMAC-SHA-256

`main` runs `HmacSha256Jasmin.runEmit`, which reads the SHA-256 bundle from
`/tmp/sha256_jasmin_full.rs`, appends the HMAC functions, and writes the result to
`/tmp/hmac_sha256_jasmin.rs`.
-/

@[expose] public section
/-- Driver script: `lake env lean --run …/HmacSha256JasminEmit.lean`. -/
private def main : IO Unit :=
  CatCrypt.Crypto.Jasmin.Examples.HmacSha256Jasmin.runEmit
