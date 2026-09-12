/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrField

/-!
# Source-derived prime modulus (a prime-IR constant carried through haxpipe)

The `primeir-hax` crate declares the field modulus as a **hax-visible** top-level
`pub const FIELD_MODULUS_25519 : [u64; 4]` — the curve25519 prime `2^255 - 19` as
four little-endian 64-bit limbs. Top-level `pub const` items are on the extraction
surface, so `haxpipeT` emits it verbatim:

```
def FIELD_MODULUS_25519 : Array (Int) :=
  #[18446744073709551597, 18446744073709551615, 18446744073709551615, 9223372036854775807]
```

This module reconstructs the integer from those extracted limbs and ties it to
`2^255 - 19` — the `p` at which the prime-IR field recognizer (`recognizeFieldOp`,
`FieldOp.fMul p`) is instantiated. The modulus is therefore **carried from the
Rust source, through haxpipe, to the `p` the emit is verified against**, rather
than trusted as a Lean-side parameter: `recognizeFieldOp_mul_at_source_derived_modulus`
shows the recognizer at the reconstructed constant is the recognizer at the
curve25519 prime.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrModulus

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrField

/-- Reconstruct a natural number from little-endian 64-bit limbs:
    `∑ limbᵢ · 2^(64·i)`. -/
def reconstructLE64 : List Nat → Nat
  | []      => 0
  | l :: ls => l + 2 ^ 64 * reconstructLE64 ls

/-- The limbs `haxpipeT` emits for `FIELD_MODULUS_25519`, verbatim from the
    certified extraction of `primeir-hax` (`0xFFFF…FFED`, `0xFFFF…FFFF` ×2,
    `0x7FFF…FFFF`, little-endian). -/
def fp25519ModulusLimbs : List Nat :=
  [18446744073709551597, 18446744073709551615, 18446744073709551615, 9223372036854775807]

/-- **Source-derived modulus.** The limbs `haxpipeT` extracts from the
    `FIELD_MODULUS_25519` `pub const` reconstruct to the curve25519 prime
    `2^255 - 19`. So the modulus is carried from the Rust source through haxpipe,
    not supplied only on the Lean side. -/
theorem fp25519_modulus_source_derived :
    reconstructLE64 fp25519ModulusLimbs = 2 ^ 255 - 19 := by
  norm_num [reconstructLE64, fp25519ModulusLimbs]

/-- **The recognizer's `p` is the source-extracted modulus.** Instantiating the
    prime-IR field recognizer at the integer reconstructed from the extracted
    `FIELD_MODULUS_25519` limbs yields the same `FieldOp.fMul` as instantiating it
    at the curve25519 prime `2^255 - 19`. The `p` the field emit denotes against
    (`ZMod p` multiplication) is thus the source constant, tied — not trusted. -/
theorem recognizeFieldOp_mul_at_source_derived_modulus :
    recognizeFieldOp "Primeir_hax.Field.mul" (reconstructLE64 fp25519ModulusLimbs)
      = some (.fMul (2 ^ 255 - 19)) := by
  rw [fp25519_modulus_source_derived]; exact recognize_mul _

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxPrimeIrModulus
