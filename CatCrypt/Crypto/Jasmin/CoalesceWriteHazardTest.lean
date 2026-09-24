/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.JasminEmit
public import CatCrypt.Crypto.Jasmin.JasminEmit

/-!
# Coalescer write-hazard regression test

Confirms `coalesceGo` refuses the unsound copy-merge that would miscompile
the Pasta Montgomery reduce's conditional subtract: merging
`x := y OP z` into `y` and renaming `x → y` in the tail when `y` is itself
**re-defined** later in the tail.
-/

@[expose] public section

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.Emit

namespace CatCrypt.Crypto.Jasmin.CoalesceWriteHazardTest

set_option autoImplicit false

def u64v (x : String) : VarI := { var := { vname := x, vtype := .sword .U64 }, info := {} }
def pv (x : String) : PExpr := .Pvar { gv := u64v x, gs := false }
def lv (x : String) : LVal := .Lvar (u64v x)
def add (d a b : String) : InstrR :=
  .Cassgn (lv d) .AT_none (.sword .U64) (.Papp2 (.Oadd .U64) (pv a) (pv b))
def cpy (d s : String) : InstrR :=
  .Cassgn (lv d) .AT_none (.sword .U64) (pv s)

/-- The write-hazard body:
    `x := y + z`  -- coalesce candidate: `y` not read again, not live-out
    `y := w + w`  -- but `y` IS RE-DEFINED here
    `out := x + x` -- a use of `x`; renaming `x → y` would read the *new* `y`.
    The merge must be REFUSED. -/
def hazardBody : List InstrR :=
  [ add "x" "y" "z"
  , add "y" "w" "w"
  , add "out" "x" "x" ]

/-- `out` is the only live-out. -/
def liveOut : List Var := [(u64v "out").var]

/-- The coalescer must NOT have renamed the use of `x` to `y` (which would make
    `out` read the re-defined `y` instead of the original `x = y + z`). So the
    merge is refused and the output still reads `x` twice (the `out := x + x`
    assignment is untouched). A guard that let the merge fire would give
    `countReads "x" = 0` — a value corruption that produces the wrong
    select. -/
theorem hazard_refused :
    countReads "x" (coalesceGo liveOut hazardBody).1 = 2 := by native_decide

/-- A control: when `y` is NOT re-defined, the legitimate merge still fires
    (`x := y + z` → `y := y + z`, then `out := y + y`), so `x` is fully
    eliminated and `y` is read three times — the fix is not over-conservative. -/
def okBody : List InstrR :=
  [ add "x" "y" "z"
  , add "out" "x" "x" ]

theorem ok_still_merges :
    countReads "x" (coalesceGo liveOut okBody).1 = 0
      ∧ countReads "y" (coalesceGo liveOut okBody).1 = 3 := by native_decide

end CatCrypt.Crypto.Jasmin.CoalesceWriteHazardTest
