/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Sha256CompressCatCryptEmit

/-!
# The SLH-DSA (SPHINCS+) WOTS+ hash chain routed through `catCryptDialect`

[`Sha256CompressCatCryptEmit.lean`](Sha256CompressCatCryptEmit.lean) builds the
**whole** FIPS 180-4 §6.2 SHA-256 compression natively as a structural
composition over `Com catCryptDialect` round-mixing programs, and proves the
composite equals the FIPS reference (`sha256Compress_catcrypt_denote`). That is
the *committed hash through the high dialect*.

This file uses that committed hash as the tweakable-hash building block `F` of a
**WOTS+ hash chain** — the core primitive of SLH-DSA / SPHINCS+ (FIPS 205,
liboqs / PQClean `slh-dsa` benchmarked). SLH-DSA is hash-based: WOTS+ advances a
chain value by *iterating* the tweakable hash `F`,

```
chain(x, s) = F^s(x)       (FIPS 205 §4.1, Algorithm 4 `chain`)
```

i.e. the chain at position `s` is `F` applied `s` times. For the SLH-DSA-SHA2
parameter sets `F` is built on the SHA-256 compression function, so we instantiate
`F` with the committed catCryptDialect compression `sha256CompressCat` (the tweak
— the ADRS / `PK.seed` material — is held fixed in the message-block / constant
parameters `m`, `k`, which thread unchanged through the chain).

## Structural composition (NOT a monolithic `Com`; mirror `chachaCoreCatCrypt`)

A single straight-line `Com catCryptDialect` for `F^s` would be `s` copies of the
whole 64-round compression (thousands of de-Bruijn ops each), which is neither
hand-authorable nor `rfl`-closable. Instead — exactly as
`Chacha20BlockCatCryptEmit.chachaCoreCatCrypt` folds the committed quarter-round
`Com` over the ten double-rounds with `Function.iterate`, and as
`runRoundsCat` folds the committed round over the 64 SHA-256 rounds — the chain is
the `Function.iterate` of the committed-hash step `F`:

1. **`wotsF` / `wotsFSpec`** (`§1`) — one chain step: the committed
   catCryptDialect compression `sha256CompressCat` (resp. the FIPS reference
   `sha256CompressSpec`) applied to the chain's working-word value with the
   chain's fixed tweak `(k, m)`. The single point where the high dialect does the
   hash; `wotsF_eq` collapses it to the reference step by the committed
   `sha256Compress_catcrypt_denote` theorem.

2. **`wotsChainCat` / `wotsChainSpec`** (`§2`) — the chain `chain(x, s) = F^s(x)`
   as `wotsF^[s]` (resp. `wotsFSpec^[s]`), the FIPS 205 §4.1 iterated chain. The
   trip count `s` is the (public) Winternitz digit.

3. **`wotsChainCat_denote`** (`§3`) — the main theorem: the catCrypt chain equals the
   reference chain, for **every** position `s`, proved by structural induction on
   `s` (the `Function.iterate` fold), composing the committed step equality
   `wotsF_eq` — NOT a monolithic `rfl` over `s` copies of the compression.

4. **`wotsChainCat_succ` / `_zero` / `_add`** (`§4`) — the FIPS 205 chain laws
   (`chain(x, 0) = x`, `chain(x, s+1) = F(chain(x, s))`,
   `chain(x, a+b) = chain(chain(x, a), b)`), free from `Function.iterate`, so the
   public-key-side full chain (`s = w-1`) and the signing-side partial chain
   compose by the additive law.

Every chain step in the whole chain is evaluated by the committed
`Com catCryptDialect` SHA-256 compression, so the WOTS+ chain — the iterated
committed hash — routes through the high `catCryptDialect` surface.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.SlhdsaWotsChainCatCryptEmit

open CatCrypt.Crypto.SecureCompilation.VIR.Sha256CompressCatCryptEmit
open CatCrypt.Util.Sha256Verified (Sha256Working)

/-! ## 1. One WOTS+ chain step: the committed catCryptDialect SHA-256 compression

The tweakable hash `F` of SLH-DSA-SHA2 is built on the SHA-256 compression. One
chain step applies `F` to the chain value `x` with the chain's fixed tweak,
modeled as the fixed compression parameters `(k, m)` (the round constants and the
ADRS/seed-derived message block — held fixed for the duration of one chain). The
catCrypt step uses the committed `sha256CompressCat`; the reference step the FIPS
`sha256CompressSpec`. -/

/-- One WOTS+ chain step over the **committed catCryptDialect** SHA-256
    compression: `F(x) = compress(x ; k, m)` with the chain's fixed tweak `(k, m)`.
    `sha256CompressCat` evaluates every `Σ₀/Σ₁/Ch/Maj/σ₀/σ₁` by the committed
    `Com catCryptDialect` programs. -/
def wotsF (k : RoundConst) (m : Fin 16 → BitVec 32) (x : Sha256Working) : Sha256Working :=
  sha256CompressCat k x m

/-- One WOTS+ chain step over the FIPS reference SHA-256 compression. -/
def wotsFSpec (k : RoundConst) (m : Fin 16 → BitVec 32) (x : Sha256Working) : Sha256Working :=
  sha256CompressSpec k x m

/-- **The catCrypt chain step equals the FIPS reference step.** The committed
    whole-compression theorem `sha256Compress_catcrypt_denote`. -/
theorem wotsF_eq (k : RoundConst) (m : Fin 16 → BitVec 32) (x : Sha256Working) :
    wotsF k m x = wotsFSpec k m x :=
  sha256Compress_catcrypt_denote k x m

/-- The catCrypt step *function* equals the reference step function (the `funext`
    form, fed to `Function.iterate_congr` below). -/
theorem wotsF_eq_fun (k : RoundConst) (m : Fin 16 → BitVec 32) :
    wotsF k m = wotsFSpec k m :=
  funext (wotsF_eq k m)

/-! ## 2. The WOTS+ chain `chain(x, s) = F^s(x)` as an iterate of the committed hash

FIPS 205 §4.1 Algorithm 4 (`chain`): the chain at position `s` is `F` applied `s`
times. We build it as `Function.iterate` of the committed-hash step `wotsF` —
exactly the `chachaCoreCatCrypt = doubleRoundCatCrypt^[10]` idiom. The reference
chain iterates `wotsFSpec`. -/

/-- The WOTS+ chain `chain(x, s) = F^s(x)` over the **committed catCryptDialect**
    SHA-256 compression: `wotsF k m` iterated `s` times. The position `s` is the
    (public) Winternitz digit `∈ [0, w-1]`. Every step is the committed hash. -/
def wotsChainCat (k : RoundConst) (m : Fin 16 → BitVec 32) (s : Nat)
    (x : Sha256Working) : Sha256Working :=
  (wotsF k m)^[s] x

/-- The WOTS+ chain over the FIPS reference compression: `wotsFSpec k m` iterated
    `s` times. The reference spec the catCrypt chain is proved equal to. -/
def wotsChainSpec (k : RoundConst) (m : Fin 16 → BitVec 32) (s : Nat)
    (x : Sha256Working) : Sha256Working :=
  (wotsFSpec k m)^[s] x

/-! ## 3. The main theorem: the catCrypt chain equals the reference chain

The deliverable. The catCrypt chain `F^s` equals the reference chain at **every**
position `s`, proved by composing the committed step equality `wotsF_eq_fun`
through the iterate (`Function.iterate_congr`), NOT a monolithic `rfl` over `s`
copies of the 64-round compression. Mirrors `chachaCoreCatCrypt_eq`. -/

/-- **WOTS+ chain theorem** (`wotsChainCat_denote`). The WOTS+ hash chain
    `chain(x, s) = F^s(x)` computed over the committed catCryptDialect SHA-256
    compression equals the FIPS reference chain, for **every** chain position
    `s ∈ [0, w-1]`. Every chain step is evaluated by the committed
    `Com catCryptDialect` SHA-256 compression `sha256CompressCat`, so the whole
    WOTS+ hash chain — the iterated committed hash — routes through the high
    dialect. Proved by folding the per-step theorem `sha256Compress_catcrypt_denote`
    through the `Function.iterate` (`congrArg (·^[s] x)`), not by unrolling. -/
theorem wotsChainCat_denote (k : RoundConst) (m : Fin 16 → BitVec 32) (s : Nat)
    (x : Sha256Working) :
    wotsChainCat k m s x = wotsChainSpec k m s x := by
  simp only [wotsChainCat, wotsChainSpec, wotsF_eq_fun]

/-! ## 4. The FIPS 205 chain laws (free from `Function.iterate`)

The defining recurrences of `chain`: identity at `0`, one more step at `s+1`, and
the additive composition `chain(x, a+b) = chain(chain(x, a), b)`. These let the
signing-side partial chain and the public-key-side completion compose. -/

/-- `chain(x, 0) = x`: the chain at the bottom of its Winternitz interval is the
    identity (no hash applications). -/
@[simp] theorem wotsChainCat_zero (k : RoundConst) (m : Fin 16 → BitVec 32)
    (x : Sha256Working) : wotsChainCat k m 0 x = x := rfl

/-- `chain(x, s+1) = F(chain(x, s))`: one more chain step is one more committed-hash
    application (FIPS 205 §4.1 step recurrence). -/
theorem wotsChainCat_succ (k : RoundConst) (m : Fin 16 → BitVec 32) (s : Nat)
    (x : Sha256Working) :
    wotsChainCat k m (s + 1) x = wotsF k m (wotsChainCat k m s x) := by
  simp only [wotsChainCat, Function.iterate_succ_apply']

/-- `chain(x, a+b) = chain(chain(x, a), b)`: the additive chain law, so the
    public-key-side full chain composes the signing-side partial chain with its
    completion (`chain(x, w-1) = chain(chain(x, d), w-1-d)`). -/
theorem wotsChainCat_add (k : RoundConst) (m : Fin 16 → BitVec 32) (a b : Nat)
    (x : Sha256Working) :
    wotsChainCat k m (a + b) x = wotsChainCat k m b (wotsChainCat k m a x) := by
  simp only [wotsChainCat, Nat.add_comm a b, Function.iterate_add_apply]

end CatCrypt.Crypto.SecureCompilation.VIR.SlhdsaWotsChainCatCryptEmit
