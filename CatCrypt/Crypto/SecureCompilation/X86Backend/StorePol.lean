/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

@[expose] public section

set_option autoImplicit false

/-!
# The store policy of a block

A store policy states the stores a block may make besides those to its frame: a red zone of
bytes below the frame, and out windows, each a base register with the bounds of the
displacements from it. The keep check `Callee.keepCheckWB` reads it, and a linked function
(`Hax.LinkedFn.pol`) declares the policy of its code.

## Main definitions

* `StorePol`: the red zone and the out windows of a block.
* `StorePol.frame`: the policy of the frame alone.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Callee

/-- The store policy of a block: the stores it may make besides those to its frame. A store
    at the stack register may reach `red` bytes below the frame (the red zone), and a store
    at the base register `b` of an out window `(b, lo, hi)` is to a word at a displacement
    `o` from `b` with `lo ≤ o` and `o + 8 ≤ hi`. -/
structure StorePol where
  /-- The size of the red zone below the frame. -/
  red : Nat
  /-- The out windows: a base register and the bounds of the displacements from it. -/
  wins : List (String × Int × Int)

/-- The store policy of the frame alone: no red zone and no out windows. -/
def StorePol.frame : StorePol := ⟨0, []⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
