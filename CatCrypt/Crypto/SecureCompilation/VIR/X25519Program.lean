/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptPrint

/-!
# X25519 field-element shape

The Curve25519 field element `Fp25519` modeled as a `memref 5`
(32 bytes = 5×64-bit limbs for the reduced representation). This is the
shape shared by the Ed25519 emit-correctness chain (`FieldExpChain` and
its semantics).
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.X25519Program

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ## Shape of a single field element -/

/-- A 5-limb representation of `Fp25519`. Matches fiat-crypto's packed
    5×51-bit layout (bits_per_word = 51, num_words = 5) or the 4×64-bit
    canonical. We use `memref 5` which is upward-compatible. -/
abbrev Fp25519 := CryptoTy.memref 5

end CatCrypt.Crypto.SecureCompilation.VIR.X25519Program
