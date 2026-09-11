/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.KernelSyntax
public import CatCrypt.Crypto.SecureCompilation.Fe25519OrchestrationSyntax

/-!
# The two-language authoring front, end state: a program written DIRECTLY in the surfaces

The two concrete surfaces are:

* **`kernel%`** (`VIR/KernelSyntax.lean`) — the dialect-generic typed
  symbol-table elaborator for a straight-line `Com` leaf;
* **`orch%`** (`Fe25519OrchestrationSyntax.lean`) — the orchestration surface
  (`RFor` over `RCall`/`RCallN` leaf calls) over the `LowCT` IR. Its
  covered-fragment extension (`RIfNz`/`RForRuntime`/`RScalarSetExpr`/… via the
  `{| … |}` block) lives in the sibling `Fe25519OrchestrationSurface.lean`.

The prototype files that introduced them pair every production with an
`= raw-AST` `rfl`. **That per-program `rfl` is transition scaffolding, not the
end state.** The elaborators are transparent AST builders; their correctness is
established ONCE by the fixed regression suites that ship with them:

* `KernelSyntax.macColKernel_eq_hand` / `addLimbKernel_eq_hand` — `kernel%` on
  two distinct op/type shapes, `rfl`-equal to hand-written `Com` leaves;
* `Fe25519OrchestrationExample.orchSyntax_eq_raw` /
  `orchStmt_callN_eq_raw` / `orchStmt_call_eq_raw` — `orch%` per-constructor and
  a full loop, `rfl`-equal to the raw `LowCT` (the fuller covered-fragment
  suite `surf_*_eq_raw` / `ladderStep_eq_raw` is in the sibling surface file).

Those suites test *the elaborators*. Once you trust them, you author programs by
**writing the surface term as the definition** — no raw twin, nothing to prove
per program. This file is that end state: a small but complete two-language
program where the surface IS the definition.

## The program

A fe25519 multiply-accumulate: an orchestration loop that, for each column,
calls a MAC-column leaf and folds the partial into the accumulator. The **leaf**
`macColumn` is authored in `kernel%` (a `Com jasminDialect` word kernel); the
**orchestration** `macAccumulate` is authored in `orch%` (a `LowCT` loop) and
calls the leaf **by name** (`mac_column`). The two languages meet at the
call boundary — exactly as the real front links a compiled leaf to its
orchestration by symbol name.

No `= raw-AST` theorem appears below. The definitions type-check against the
`Com jasminDialect …` / `LowCT` signatures; that they elaborate at all is the
authoring guarantee, and the elaborator regression suites (imported above)
supply the trust that the elaboration is faithful.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Fe25519TwoLanguageProgram

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.KernelSyntax
open CatCrypt.Crypto.SecureCompilation.Fe25519OrchestrationExample

/-! ## 1. The leaf, authored in `kernel%`

The fe25519 MAC-column low word `acc_lo + a·b`: multiply `a·b`, add into the
running low accumulator. Written with named formals and named bindings; the
elaborator resolves each name to its typed de-Bruijn `Ctxt.Var`. The surface is
the definition. -/

/-- The MAC-column low-word leaf, authored directly in `kernel%`. -/
def macColumn : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  kernel% (acc_lo : .reg 64) (acc_hi : .reg 64) (a : .reg 64) (b : .reg 64) {
    p_lo := (JasminOp.regArith .mul 64) [a, b];
    s    := (JasminOp.regArith .add 64) [acc_lo, p_lo];
    ret s
  }

/-! ## 2. The orchestration, authored in `orch%`, calling the leaf by name

A bounded loop over columns: each iteration multiplies the operand pair
`(a_i, b_i)` through the `mac_column` leaf into partial `p`, then accumulates
`p` into `acc` via the field add. `callN mac_column(…)` references the leaf
authored in §1 by its symbol name. The surface is the definition. -/

/-- The multiply-accumulate orchestration over `n` columns, authored directly in
    `orch%`. Calls the `macColumn` leaf by name (`mac_column`). -/
def macAccumulate (n : Nat) : LowCT :=
  orch% for "i" in 0.. n {|
    "p"   := callN mac_column("a_i", "b_i");
    "acc" := call  fe25519_add("p")
  |}

end CatCrypt.Crypto.SecureCompilation.Fe25519TwoLanguageProgram
