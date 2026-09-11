/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCDSL

/-! Re-export of `CatCryptCore.Crypto.UCDSL` from the CatCrypt-core package, so existing
`import CatCrypt.Crypto.UCDSL` lines resolve to the upstream library. The enhanced UC DSL
combinators (`UCProtocol.ofGame`, `UCEmulates_of_isPure_advantage`, `sdist_game_hop₂`,
`uc_alg_comp`, …) live in the `CatCrypt.Crypto.UCDSL` namespace provided by the upstream
module. -/

@[expose] public section
