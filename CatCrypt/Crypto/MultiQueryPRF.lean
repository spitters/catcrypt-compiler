/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MultiQueryPRF

/-! Re-export of `CatCryptCore.Crypto.MultiQueryPRF` from the CatCrypt-core package, so
existing `import CatCrypt.Crypto.MultiQueryPRF` lines resolve to the upstream library. The
`q`-fold hybrid argument for a `q`-query PRF adversary (`prf_multi_query_bound`,
`prf_multi_query_perfect`, `prf_multi_query_nested`) lives in the
`CatCrypt.Crypto.MultiQueryPRF` namespace provided by the upstream module. -/

@[expose] public section
