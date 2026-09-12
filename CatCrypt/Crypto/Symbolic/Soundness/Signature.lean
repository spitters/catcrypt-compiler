/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Soundness.CoinductiveAttacker

/-!
# Computational Soundness for Signatures

**Status: TRIVIAL — single `rfl` theorem stating signatures are public.**

Signatures have label `.top` (always public). The EUF-CMA assumption would
become relevant in a property-lifting phase (not yet implemented) when
authentication correspondences are lifted from symbolic to computational.

## References

* Cortier, Warinschi (2005), §4 — signature soundness
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Soundness

open CatCrypt.Crypto.Symbolic

/-- Signatures are always timed-publishable: `timedLabelOf(.sign _ _ _) = .top`.
This means they contribute no secrecy constraints in the soundness proof.
The authentication contribution comes from EUF-CMA in the property lifting phase. -/
theorem sign_always_public (tr : Trace) (sk nonce msg : Bytes) :
    labelOf tr (.sign sk nonce msg) = .top := rfl

end CatCrypt.Crypto.Symbolic.Soundness
