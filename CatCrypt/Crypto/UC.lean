/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UC

/-! Re-export of `CatCryptCore.Crypto.UC` from the CatCrypt-core package, so existing
`import CatCrypt.Crypto.UC` lines resolve to the upstream library. The UC-emulation
definitions and lemmas (`UCSpec`, `UCEmulates`, `UCEmulates_of_sdist`, `UCEmulates_trans`,
`GameUCEmulates`, …) live in the `CatCrypt.Crypto` namespace provided by the upstream
module. The concurrent (ITreeN) UC layer remains in this repository under
`CatCrypt/Crypto/UCMonad/`. -/

@[expose] public section
