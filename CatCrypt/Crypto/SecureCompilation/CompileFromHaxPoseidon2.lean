/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the Poseidon2 round-loop body from extracted source

This module re-derives the **Poseidon2-BabyBear round-loop body**
(`Poseidon2Emit.roundLoopBody`) *through* the verified compile-from-hax front,
rather than hand-authoring it as a `Com`.

`roundLoopBody` is the multi-op `regArith` linear-arithmetic core that the MDS
layer's repeated additions reuse (`Poseidon2Emit.lean §3`): two fresh SSA
binders over a `reg 64` accumulator,

```
v0 = acc + acc     -- regArith add
v1 = v0  + v0      -- regArith add
return v1          -- = 4·acc  (mod 2^64)
```

Its op-set is **scalar add only** — pure ARX in the narrowest sense. The field
machinery that Poseidon2 *also* needs (`bbFold`/`bbMul`/`bbReduce`: the
shift-multiply-mask reduction, the `x^7` S-box, the modular product) lives in
*separate* definitions in `Poseidon2Emit.lean`; **none of it is in
`roundLoopBody`**. So this particular body is squarely in front-scope, and we
emit it from extracted source exactly as the SHA-256 / Keccak / BLAKE2 leaves do
(`CompileFromHaxLeaves` / `CompileFromHaxKeccak` / `CompileFromHaxBlake2`).

## The body source (w = 64, one input)

The accumulator-doubling body is two wrapping adds over a single `reg 64` input
`x` (the accumulator). The closed form is `4·x` over `BitVec 64`. The single
input means `nIn = 1`, `["x"]`; the `reg 64` lane means `w = 64`.

## Method (mirrors `CompileFromHaxBlake2.blake2G_compiles`)

1. `roundBodySrc` — a let-normalized `ImpExpr` source: `v0 = x+x`, `v1 = v0+v0`.
2. `roundBodySpec` — the explicit closed form (`= 4·x` over `BitVec 64`).
3. `roundBodySrc_denoteScalar` — the source `denoteScalar` computes `roundBodySpec`.
4. `roundBody_compileFromHax_isSome` — the compile succeeds (`native_decide`).
5. `roundBody_compiles` — the emitted jasmin `Com` denotes to `roundBodySpec`,
   routed through the C3 per-primitive obligation `compileFromHax_meets_spec`.

The emitted jasmin `Com` is *computed by the verified compiler from the extracted
source*, proven equal to the `4·acc` value that `Poseidon2Emit.roundLoopBody`'s
two-binder `regArith add` chain computes — with no front change beyond the
existing `wrapping_add` recognizer.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxPoseidon2

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## The Poseidon2 round-loop body — accumulator doubling

Parameter `["x"]` (`nIn = 1`; `I 0 = x` is the accumulator), at `w = 64`. The
body binds `v0 = x + x` then `v1 = v0 + v0`, returning `v1` — two `wrapping_add`s
over atom arguments, mirroring `Poseidon2Emit.roundLoopBody`'s two `regArith add`
binders over `acc = .here`. -/

/-- The Poseidon2 round-loop body source as a hax `ImpExpr`, fully let-normalized,
    parameter `["x"]`. Two `wrapping_add` binders: `v0 = x + x`, `v1 = v0 + v0`.
    Mirrors `Poseidon2Emit.roundLoopBody` (`v0 = acc + acc`, `v1 = v0 + v0`,
    `ret v1`). -/
def roundBodySrc : ImpExpr :=
  .letBind "v0" (.app "wrapping_add" [.var "x", .var "x"])
    (.letBind "v1" (.app "wrapping_add" [.var "v0", .var "v0"])
      (.var "v1"))

/-- The explicit closed form of the round-loop body at `w = 64`: bind `v0 = x+x`,
    `v1 = v0+v0`, return `v1` — i.e. `4·x` over `BitVec 64`. Stated as a plain
    `def` so the spec is explicit and auditable. This is the same value
    `Poseidon2Emit.roundLoopBody`'s two `regArith add` binders compute. -/
def roundBodySpec (x : BitVec 64) : BitVec 64 :=
  let v0 := x + x
  let v1 := v0 + v0
  v1

/-- The closed form equals `4·x`: the documented `roundLoopBody` semantics. -/
theorem roundBodySpec_eq_four (x : BitVec 64) : roundBodySpec x = 4 * x := by
  simp only [roundBodySpec]; ring

/-- The round-body source denotes (under `denoteScalar`, parameter `["x"]`) to the
    closed form `roundBodySpec`, reading `x = inpGet I 0`. The closed
    let-normalized body reduces; `wrapping_add` is `+`. -/
theorem roundBodySrc_denoteScalar (I : Fin 1 → BitVec 64) :
    ImpExpr.denoteScalar ["x"] I roundBodySrc (fun _ => none)
      = some (roundBodySpec (inpGet I 0)) := by
  -- The closed let-normalized `denoteScalar` chain and `roundBodySpec` both reduce
  -- definitionally (the string lookups and the `recogBin` recognizer compute on
  -- the closed source), so the source-spec is a `rfl`.
  rfl

/-- The compile-from-hax pipeline succeeds on the round-loop body (`w = 64`, one
    parameter). -/
theorem roundBody_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 1) ["x"] roundBodySrc).isSome := by
  native_decide

/-- **The Poseidon2 round-loop body emitted by the verified compiler.** There is a
    compiled `Com jasminDialect` `c` with
    `compileFromHax ["x"] roundBodySrc = some c`, and for every accumulator `x`,
    `c`'s `BitVec 64` denotation (under the input valuation `fun _ => x`) is exactly
    the closed form `roundBodySpec x = 4·x` — the value
    `Poseidon2Emit.roundLoopBody`'s two `regArith add` binders compute. Routed
    through the C3 per-primitive obligation `compileFromHax_meets_spec`. This
    re-derives the previously hand-authored `roundLoopBody` *through* the verified
    front: the compiler authors the body from extracted source, reusing the
    SHA-256 / BLAKE2 `wrapping_add` recognizer with no front change. -/
theorem roundBody_compiles :
    ∃ (c : Com jasminDialect (frontCtxt 64 1 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 1) ["x"] roundBodySrc = some c ∧
      ∀ (x : BitVec 64),
        c.denote (inputValuation 64 1 (fun _ => x))
          = roundBodySpec x := by
  set c := (compileFromHax (w := 64) (nIn := 1) ["x"] roundBodySrc).get
    roundBody_compileFromHax_isSome with hc_def
  have hc : compileFromHax (w := 64) (nIn := 1) ["x"] roundBodySrc = some c :=
    (Option.some_get _).symm
  refine ⟨c, hc, ?_⟩
  intro x
  have hspec := roundBodySrc_denoteScalar (fun _ => x)
  exact compileFromHax_meets_spec (w := 64) (nIn := 1) ["x"] (fun _ => x)
    roundBodySrc _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxPoseidon2
