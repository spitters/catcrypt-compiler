/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.HaxToThirFront
public import CatCrypt.Crypto.SecureCompilation.HaxToThirFront
public meta import CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
public import CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction

/-!
# Front ingestion lands in the index-free (CT-by-construction) jasmin fragment

This file ties `HaxToThirFront.impToJasmin` (source `ImpExpr → Com jasminDialect`)
to `JasminCTByConstruction`: for an arithmetic/ARX source body, the `Com
jasminDialect` the front produces contains **no** `stackLoad` / `stackStore`, so
it is constant-time by construction — `ComJasminCTByConstruction` holds with no
side condition.

## Scope (honest)

The front lowering also supports *runtime-indexed* gathers (e.g. an NTT ζ-table
`stackLoad` at a computed index), which are **not** index-free — those are CT only
when the index register is public (the `LowCTCTAnalysis` obligation owned by the
backend workstream; see the `stackLoad`/`stackStore` "CT-safe iff `.Public` index"
note in `ThirToComFront`). So there is no *unconditional* "front output is always
index-free" theorem.

What holds, and is shown here, is the structural half: a body in the
let-normalized scalar ARX subset (literals, input-register reads, ALU ops,
immediate shifts/rotates) lowers to register-only jasmin
(`regArith` / `mulhi` / `regConst` / shifts) — the index-free fragment — for which
`ComJasminCTByConstruction` is discharged with `comJasminCT?` + `native_decide`,
no public-index hypothesis required. The worked example is `HaxToThirFront.maddSrc`
(`(w[0]*w[1]) + w[0]`), the same body whose value-correctness
(`maddSrc_front_e2e`) the front already proves.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FrontJasminCT

open CatCrypt.Crypto.SecureCompilation.HaxToThirFront
open CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
open CatCrypt.Crypto.SecureCompilation.ThirToComFront (frontCtxt rW)
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-- The `Com jasminDialect` the front produces for the worked-example arithmetic
    body is in the **index-free fragment**: `comJasminCT?` accepts it. -/
theorem maddSrc_front_comJasminCT? :
    comJasminCT? ((impToJasmin 64 2 ["w"] maddSrc).get maddSrc_compiles) = true := by
  native_decide

/-- **Front ingestion produces CT-by-construction jasmin (arithmetic subset).**
    There is a `Com jasminDialect` `c` such that the hax source `(w[0]*w[1]) + w[0]`
    ingests through the front entry to `c`, and `c` is constant-time by
    construction — it binds no `stackLoad` / `stackStore`, so no secret can create
    an address/timing channel, with **no** public-index side condition. -/
theorem maddSrc_front_ct_by_construction :
    ∃ c : Com jasminDialect (frontCtxt 64 2 []) (rW 64),
      impToJasmin 64 2 ["w"] maddSrc = some c ∧ ComJasminCTByConstruction c := by
  refine ⟨(impToJasmin 64 2 ["w"] maddSrc).get maddSrc_compiles,
          (Option.some_get _).symm, ?_⟩
  exact (comJasminCT?_eq_true_iff _).mp maddSrc_front_comJasminCT?

end CatCrypt.Crypto.SecureCompilation.FrontJasminCT
