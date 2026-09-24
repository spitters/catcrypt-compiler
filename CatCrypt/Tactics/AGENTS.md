# `CatCrypt/Tactics/`: re-exported proof tactics

Most modules here re-export a tactic module of the
[CatCrypt-core](https://github.com/spitters/CatCrypt-core) package under the name
`CatCrypt.Tactics.<Name>`, so that `import CatCrypt.Tactics.<Name>` resolves in this
package. The tactic and its documentation live in `CatCryptCore.Tactics.<Name>`.

## Re-exports of CatCrypt-core

`Auto`, `Basic`, `BindAlign`, `BindMatch`, `BindVcgen`, `BindVcgenSum`, `BridgeGen`,
`Call`, `Conditional`, `CryptoAuto`, `EnvSearch`, `FieldClear`, `Invariant`,
`LazySampling`, `LeOfSum`, `Proc`, `ProofFrog`, `ProofTermAudit`, `RSpec`, `Remember`,
`Restore`, `SP`, `SPNormalize`, `Sim`, `SimpAttr`, `SumCases`, `Sync`, `Triangle`,
`TryBij2`, `UpToBad`, `VC`, `WP`; and [`PkgCoherenceBang`](PkgCoherenceBang.lean),
the `pkg_coherence!` tactic for package coherence goals.

## Modules defined here

| Module | Contents |
|---|---|
| [`BvToNat`](BvToNat.lean) | the `BitVec` → `Nat` coercion library behind `poly_zp` |
| [`PreservationCombinator`](PreservationCombinator.lean) | one preservation combinator for chunked state updates |
| [`BvToNatE2ETest`](BvToNatE2ETest.lean), [`PolyZpTest`](PolyZpTest.lean) | checks of `poly_zp` on instruction sequences |

## Conventions

- Change a re-exported tactic in CatCrypt-core; the module here stays a one-line
  import.
- Tactics for field, bignum and matrix goals live in
  [`CatCrypt/Tactic/`](../Tactic/AGENTS.md); the ascent tactics live in
  `SecureCompilation/Ascent/` ([AGENTS.md](../Crypto/SecureCompilation/Ascent/AGENTS.md)).
