/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxPoseidon2
import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit

/-!
# #607 Phase 3 (Category-A tie): the compile-from-hax Poseidon2 round-loop body
# equals the in-tree hand-authored `Poseidon2Emit.roundLoopBody` Com

`CompileFromHaxPoseidon2.lean` proves that the verified compiler **emits** the
Poseidon2-BabyBear MDS round-loop body (the accumulator-doubling core) from
extracted `ImpExpr` source: there is a `Com jasminDialect (frontCtxt 64 1 [])`
`c` with `compileFromHax ["x"] roundBodySrc = some c` and, for every accumulator
`x`, `c.denote (inputValuation 64 1 (fun _ => x)) = roundBodySpec x`, where
`roundBodySpec x = 4·x` over `BitVec 64` (`roundBodySpec_eq_four`).

`Poseidon2Emit.roundLoopBody` is the **hand-authored** `Com jasminDialect [r64]
r64` for the same body — two `regArith add` binders `v0 = acc+acc`, `v1 = v0+v0`,
`ret v1` — the linear-arithmetic core the MDS layer's repeated additions reuse
(`Poseidon2Emit §3`, partial-round loop keystone). Its context `[r64]` is
**definitionally** `frontCtxt 64 1 []` (`= List.replicate 1 (rW 64) = [.reg 64]`),
so the compiled leaf and the hand-authored Com live in the *same* `Com` type.

This module is the **tie**: it shows the verified-compiler-emitted `Com` and the
hand-authored `roundLoopBody` Com **denote to the same function** of the
accumulator — `4·x` over `BitVec 64` — under the same input valuation:

```
   c.denote (inputValuation 64 1 (fun _ => x))
     =  roundLoopBody.denote (inputValuation 64 1 (fun _ => x))   ( = 4·x ).
```

This is the Poseidon2 analogue of `CompileFromHaxAsconTie` (emitted leaf =
independent in-tree verified `asconRound` body) and of `CompileFromHaxPlonky3Bb
Tie` (emitted `bbMul` realizes the field op the soundness layer references): the
compiler authors the round-loop body from extracted source, and it computes
exactly the value the hand-authored `roundLoopBody` does — the one the
partial-round loop keystone (`roundLoop_denote_eq`) iterates.

## Honest scope

* The tie is at the **MDS accumulator-doubling body** granularity — the linear
  `regArith` core (`4·x`). The Poseidon2 *S-box* (`x^7` via `bbMul`) and the full
  Baby Bear modular reduction (`bbFold`/`bbReduce`) live in **separate**
  `Poseidon2Emit` definitions and are **not** in `roundLoopBody`; no S-box /
  permutation-level functional tie is claimed here. This matches the existing
  `CompileFromHaxPoseidon2` leaf scope.
* This is a **functional-equality** tie (compiled `Com` = hand `Com` as functions
  of the accumulator), not a security bound. Poseidon2 is an unkeyed permutation
  component; there is no security claim here, only `<emitted> = <hand-authored>`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxPoseidon2Tie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation frontCtxt rW)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax (compileFromHax)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxPoseidon2
  (roundBodySrc roundBodySpec roundBodySpec_eq_four roundBody_compiles)
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit (roundLoopBody r64)

/-! ## §1  The hand-authored `roundLoopBody` Com denotes to `4·x`

`roundLoopBody` (`v0 = acc+acc`, `v1 = v0+v0`, `ret v1`) over `[r64]` denotes,
under the single-input valuation `inputValuation 64 1 (fun _ => x)`, to `4·x`.
Its context `[r64]` is definitionally `frontCtxt 64 1 []`, so the valuation
typechecks against it. -/

/-- The hand-authored `Poseidon2Emit.roundLoopBody` Com denotes (under the
    single-accumulator valuation) to the closed form `roundBodySpec x = 4·x`. The
    two `regArith add` binders compute `(x+x)+(x+x)`. -/
theorem roundLoopBody_denote (x : BitVec 64) :
    roundLoopBody.denote (inputValuation 64 1 (fun _ => x)) = roundBodySpec x := by
  simp only [roundBodySpec]
  rfl

/-! ## §2  The tie: emitted `Com` = hand-authored `roundLoopBody` Com (as functions)

The verified compiler emits a `Com` whose denotation equals the hand-authored
`roundLoopBody` Com's denotation, accumulator-pointwise. Both are `4·x`. -/

/-- **Poseidon2 Category-A tie.** The verified compiler emits a `Com jasminDialect
    (frontCtxt 64 1 [])` `c` on `roundBodySrc` such that for every accumulator
    `x`, `c`'s `BitVec 64` denotation equals the **hand-authored**
    `Poseidon2Emit.roundLoopBody` Com's denotation under the same valuation — both
    are `roundBodySpec x = 4·x`:

    `c.denote (inputValuation 64 1 (fun _ => x))
        = roundLoopBody.denote (inputValuation 64 1 (fun _ => x))`.

    The compiler authors the round-loop body from extracted source, and it
    computes exactly the value the hand-authored `roundLoopBody` does — the body
    the partial-round loop keystone (`roundLoop_denote_eq`) iterates.
    Functional-equality tie; MDS-doubling-body scope (no S-box / permutation
    claim). -/
theorem emittedRoundBody_eq_roundLoopBody :
    ∃ (c : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["x"] roundBodySrc = some c ∧
      ∀ (x : BitVec 64),
        c.denote (inputValuation 64 1 (fun _ => x))
          = roundLoopBody.denote (inputValuation 64 1 (fun _ => x)) := by
  obtain ⟨c, hc, hden⟩ := roundBody_compiles
  refine ⟨c, hc, fun x => ?_⟩
  rw [hden x, roundLoopBody_denote x]

/-- **Closed form of the tie.** The emitted round-loop body equals `4·x` — the
    documented `Poseidon2Emit.roundLoopBody` semantics. Folds
    `roundBodySpec_eq_four` onto the emitted leaf. -/
theorem emittedRoundBody_eq_four :
    ∃ (c : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["x"] roundBodySrc = some c ∧
      ∀ (x : BitVec 64),
        c.denote (inputValuation 64 1 (fun _ => x)) = 4 * x := by
  obtain ⟨c, hc, hden⟩ := roundBody_compiles
  refine ⟨c, hc, fun x => ?_⟩
  rw [hden x, roundBodySpec_eq_four]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxPoseidon2Tie
