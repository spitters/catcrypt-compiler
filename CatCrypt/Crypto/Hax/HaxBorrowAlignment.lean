/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCT
public import CatCrypt.Crypto.Jasmin.LowCTBorrowCheck

/-!
# H3: Hax → LowCT borrow alignment — STUB (4.29 port)

TODO(4.29 port): under Lean 4.29 the original `HaxBorrowAlignment.lean`
overflows the elaborator stack at compile time (`Stack overflow detected.
Aborting.`) even when its proofs are stubbed out. The root cause is
likely a kernel reducibility regression triggered by the wide
`ImpExpr.ind`-shaped match expressions in `allVarsImp`, `freshLetBoundImp`,
and `borrowSafeImp` (many constructors × heavy `cases` cascades inside
the structural-induction proofs and well-founded termination checks).
Switching the defs to `partial def` and stubbing out the proofs is
insufficient — the overflow predates any tactic block.

Stubbed pending a 4.29-compatible decomposition (split per-constructor
helper defs / lemmas; or migrate `ImpExpr.ind` to a smaller induction
principle). The H3 alignment theorem statements and their corollaries
are *not* downstream-blocking for the security stack: nothing under
`CatCrypt/Crypto/Security/` imports this file directly.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

end CatCrypt.Crypto.Hax
