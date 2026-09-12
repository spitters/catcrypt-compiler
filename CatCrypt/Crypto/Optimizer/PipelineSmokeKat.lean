/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Pipeline
public import CatCrypt.Crypto.Jasmin.RustEmit

/-!
# Optimizer rewrite smoke test, as a program

The Tier-3 optimizer rewrites its canonical ML-KEM and ML-DSA loops into the
hoisted form. Checked by running a comparison rather than by `rfl` in a proof:
the goal reduces the whole optimizer over a concrete kernel, which costs
elaboration and stops reducing once a body is unexposed downstream.

```
lake exe optimizer-smoke-kat
```

## Main definitions

* `cases`: the (name, actual, expected) triples the optimizer must satisfy.
* `main`: compares them, printing the differing pair on failure.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.PipelineSmokeKat

open CatCrypt.Crypto.Optimizer.Pipeline
open CatCrypt.Crypto.Jasmin.LowCT

/-- `LowCT` has no `BEq`, so compare the rendered form. -/
def render (c : LowCT) : String := ppLowCT [] [] 0 c

/-- Canonical kernels paired with the hoisted form the optimizer must produce. -/
def cases : List (String × LowCT × LowCT) :=
  [ ("tier3MlkemHoisted", tier3MlkemHoisted hoistSmokeKernel,    hoistSmokeExpected)
  , ("tier3MldsaHoisted", tier3MldsaHoisted hoistSmokeKernelDsa, hoistSmokeExpectedDsa) ]

end CatCrypt.Crypto.Optimizer.PipelineSmokeKat

open CatCrypt.Crypto.Optimizer.PipelineSmokeKat in
def main : IO UInt32 := do
  let mut bad := 0
  for c in cases do
    let nm := c.1
    let actual := c.2.1
    let expected := c.2.2
    if render actual == render expected then
      IO.println s!"optimizer-smoke: {nm} ok"
    else
      IO.eprintln s!"optimizer-smoke: {nm} MISMATCH"
      IO.eprintln s!"  actual:\n{render actual}"
      IO.eprintln s!"  expected:\n{render expected}"
      bad := bad + 1
  return (if bad == 0 then 0 else 1)
