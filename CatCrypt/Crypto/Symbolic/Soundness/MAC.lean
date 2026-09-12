/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Symbolic.Soundness.CoinductiveAttacker

/-!
# Computational Soundness for MACs

**Status: TRIVIAL — single `rfl` theorem stating MACs are public.**

MACs have label `.top` (always public). EUF-CMA would be relevant for
authentication lifting (not yet implemented). For EDHOC, MACs are absorbed
by AEAD security; for TLS, they appear in Finished messages.
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic.Soundness

open CatCrypt.Crypto.Symbolic

/-- MACs are always public. -/
theorem mac_always_public (tr : Trace) (key msg : Bytes) :
    labelOf tr (.mac key msg) = .top := rfl

end CatCrypt.Crypto.Symbolic.Soundness
