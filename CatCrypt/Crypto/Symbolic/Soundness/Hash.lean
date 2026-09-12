/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Soundness.CoinductiveAttacker

/-!
# Computational Soundness for Hashing

**Status: TRIVIAL — single `rfl` theorem stating hashes are public.**

Hashes have label `.top` (always public). Collision resistance would become
relevant in a property-lifting phase (not yet implemented).
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Soundness

open CatCrypt.Crypto.Symbolic

/-- Hashes are always public. -/
theorem hash_always_public (tr : Trace) (msg : Bytes) :
    labelOf tr (.hash msg) = .top := rfl

end CatCrypt.Crypto.Symbolic.Soundness
