/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# Constant-time preservation for `JForProg` transforms

This module contains no declarations.

## Main results

None. Constant-time statements for the `JForProg` transforms are in other
modules:

* `JForProgCT.ctSafeJForProg_iff_body` — CT-safety of a `JForProg` is
  CT-safety of its body, so an unrolled program (`JForProgUnroll`) is CT-safe
  exactly when its unrolled body is;
* `Optimizer.RegAllocLeakTrace` (`renameBlock_preserves_leakTrace`,
  `rewriteBlock_preserves_ctLeakFree`, `raRewrite_preserves_ctLeakFree`) —
  register renaming leaves the leakage trace unchanged and inserted spill
  traffic is publicly addressed;
* `SoftwarePipeliningReal` (`steady_preserves_CT`) — CT preservation of the
  prologue-peel loop transform;
* `RobustCompilationPipeline` — lifts `Com`-level CT to the Jasmin and
  assembly levels.
-/

@[expose] public section
