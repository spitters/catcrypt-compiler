/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean

/-!
# The `@[corres]` leaf-lemma label attribute

`corres` labels the per-instruction `CorresJ` ascent leaves that `corres_solve`
(in `CorresSolver.lean`) composes over a straight-line `JInstr` block. A tagged
lemma has conclusion `CorresJ SR (fun _ => True) step [i]` for a single instruction
`i`. The attribute lives in its own file because a label attribute is usable only in
modules that import the one registering it.
-/

/-- Per-instruction `CorresJ` ascent leaves, composed by `corres_solve`. -/
register_label_attr corres
