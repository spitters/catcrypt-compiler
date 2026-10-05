/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.AscendHax
public import HaxAscent.Ascent.Demo

/-!
# `hax_corres` on two literals

`keyEq_corres_gen` is the correspondence `keyEq_corres` of
`HaxAscent/Ascent/Demo.lean` proved by one `hax_corres` call: the counted loop is given
by its invariant bindings `keyEqΛ`, the initial accumulator `true` and the step
`keyEqStep`, and the side conditions are closed with the leaf lemmas `index_enc` and
`ne_int` and the definitions of the example.

`lineLit` is a straight-line literal of twenty bindings `x_k := x_{k-1} + k` under the
builtin table `addBuiltins`; `line_corres_gen` proves its correspondence with
`lineFn a = a + 210` by `hax_corres`, and `line_corres_rules` proves the same statement by
applying the rules of `HaxAscent/Ascent/AscendHax.lean` one by one.

## Main results

* `keyEq_corres_gen`
* `line_corres_gen`, `line_corres_rules`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent.Demo

/-- The loop invariant of the comparison as bindings: `eq` holds the accumulator, `a` and
    `b` the two arrays. -/
def keyEqΛ (σ : KS) (_i : Int) (acc : Bool) : List (String × Value) :=
  [("eq", .bool acc), ("a", enc σ.1), ("b", enc σ.2)]

/-- `Ne` on two integers. -/
theorem ne_int (x y : Int) : demoBuiltins "Ne" [.int x, .int y] = some (.bool (x != y)) := rfl

/-- **The comparison by the generator.** The statement of `keyEq_corres`. -/
theorem keyEq_corres_gen :
    Corres demoBuiltins (fun env σ => env = keyEqEntry σ) keyEqGuard keyEqLit
      (fun σ => enc (keyEq σ.1 σ.2)) (fun env σ => KInv env σ 32 (keyEq σ.1 σ.2)) := by
  hax_corres [keyEqΛ, keyEqGuard, ne_int, keyEqStep, keyEq, index_enc, KInv, RA]
    loops [(keyEqΛ, fun _ => true, fun (σ : KS) => keyEqStep σ.1 σ.2)]

/-- The builtin table of the straight-line example: `Add` on integers. -/
def addBuiltins : Builtins
  | "Add", [.int x, .int y] => some (.int (x + y))
  | _, _ => none

/-- `Add` on two integers. -/
theorem add_int (x y : Int) : addBuiltins "Add" [.int x, .int y] = some (.int (x + y)) := rfl

/-- A straight-line literal of twenty bindings: `x_k := x_{k-1} + k`, the result `x20`. -/
def lineLit : ImpExpr :=
  .letBind "x1" (.app "Add" [.var "a", .lit (.int 1)]) <|
  .letBind "x2" (.app "Add" [.var "x1", .lit (.int 2)]) <|
  .letBind "x3" (.app "Add" [.var "x2", .lit (.int 3)]) <|
  .letBind "x4" (.app "Add" [.var "x3", .lit (.int 4)]) <|
  .letBind "x5" (.app "Add" [.var "x4", .lit (.int 5)]) <|
  .letBind "x6" (.app "Add" [.var "x5", .lit (.int 6)]) <|
  .letBind "x7" (.app "Add" [.var "x6", .lit (.int 7)]) <|
  .letBind "x8" (.app "Add" [.var "x7", .lit (.int 8)]) <|
  .letBind "x9" (.app "Add" [.var "x8", .lit (.int 9)]) <|
  .letBind "x10" (.app "Add" [.var "x9", .lit (.int 10)]) <|
  .letBind "x11" (.app "Add" [.var "x10", .lit (.int 11)]) <|
  .letBind "x12" (.app "Add" [.var "x11", .lit (.int 12)]) <|
  .letBind "x13" (.app "Add" [.var "x12", .lit (.int 13)]) <|
  .letBind "x14" (.app "Add" [.var "x13", .lit (.int 14)]) <|
  .letBind "x15" (.app "Add" [.var "x14", .lit (.int 15)]) <|
  .letBind "x16" (.app "Add" [.var "x15", .lit (.int 16)]) <|
  .letBind "x17" (.app "Add" [.var "x16", .lit (.int 17)]) <|
  .letBind "x18" (.app "Add" [.var "x17", .lit (.int 18)]) <|
  .letBind "x19" (.app "Add" [.var "x18", .lit (.int 19)]) <|
  .letBind "x20" (.app "Add" [.var "x19", .lit (.int 20)]) <|
  .var "x20"

/-- The shallow function of `lineLit`. -/
def lineFn (a : Int) : Int := a + 210

/-- **The straight line by the generator.** -/
theorem line_corres_gen :
    Corres addBuiltins (fun env a => env = bindParams [("a", enc a)]) (fun _ => True) lineLit
      (fun a => enc (lineFn a)) (fun _ _ => True) := by
  hax_corres [add_int, lineFn]

/-- One binding `x := y + k` of `lineLit`, by the rules. -/
local macro "line_step" : tactic => `(tactic| (
  apply corresB_letBind
  · apply corresB_app
    · apply corresArgsB_cons
      · apply corresB_var; hax_corres_side
      · hax_corres_side
      · apply corresArgsB_cons
        · exact corresB_lit _ _ _
        · hax_corres_side
        · exact corresArgsB_nil _ _
    · hax_corres_side [add_int]
  · hax_corres_side))

/-- **The straight line by the rules.** The statement of `line_corres_gen`. -/
theorem line_corres_rules :
    Corres addBuiltins (fun env a => env = bindParams [("a", enc a)]) (fun _ => True) lineLit
      (fun a => enc (lineFn a)) (fun _ _ => True) := by
  apply corres_of_corresB (fun a => [("a", enc a)])
  · unfold lineLit
    iterate 20 line_step
    apply corresB_var
    hax_corres_side
  all_goals hax_corres_side [lineFn]

end Hax.Ascent.Demo
