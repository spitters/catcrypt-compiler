/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.CryptoAuto
public import CatCrypt.Tactics.VC

/-! Re-export of `CatCryptCore.Tactics.CryptoAuto` from the CatCrypt-core package,
so existing `import CatCrypt.Tactics.CryptoAuto` lines resolve to the upstream library.
Declarations and namespaces (`CatCrypt.*`) are provided by the upstream module. -/

@[expose] public section

namespace CatCrypt.Tactics

/-- Dev-side extension of `ssprove_crypto`: also try the SPComp side-condition
    closers (`ssprove_vc`: IsPure / NoFail / pHoare via the `Std.Do` bridge),
    gated by `done` so this branch only fires when it fully closes the goal. -/
macro_rules
  | `(tactic| ssprove_crypto) => `(tactic| (ssprove_vc; done))

end CatCrypt.Tactics
