/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Soundness.CoinductiveAttacker

/-!
# Computational Soundness for KEM (Key Encapsulation Mechanism)

**Status: TRIVIAL — definitions + `rfl` label theorem.**

Defines `KEMProtected` and states that KEM public keys have label `.top`.
The actual IND-CCA hiding reduction is NOT implemented here. KEMs are
needed for post-quantum / HNDL scenarios but not for classical EDHOC.
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Soundness

open CatCrypt.Crypto.Symbolic

/-- KEM shared secrets are protected when the secret key is not accessible. -/
def KEMProtected (_tr : Trace) (S : Bytes → Prop) (sk : Bytes) : Prop :=
  ¬S sk

/-- KEM public keys are always public. -/
theorem kemPub_always_public (tr : Trace) (sk : Bytes) :
    labelOf tr (.kemPub sk) = .top := rfl

end CatCrypt.Crypto.Symbolic.Soundness
