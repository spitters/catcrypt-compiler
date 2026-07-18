/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
import CatCrypt.Crypto.SecureCompilation.Ascent.Control

/-!
# The `ascend` tactic — the integrator

Assembles the per-constructor `corres_*` database (the leaf `corres_setScalar`, the
structural `corres_seq`/`_skip`/`_block`) into a **total** ascent over the assignable
straight-line fragment `IsAscendable`, fronted by the `ascend` tactic. This is the
AutoCorres/Ascent phase pass in total form for the fragment the value leaf covers: every
`IsAscendable` program lifts to its pure word spec `asemW c` over `ZMod 2^64`, with no
manual composition.

Frontier (honest, = the descent's): the loop/conditional rules `corres_for`/`corres_if`
(`Ascent.Control`) are proved and compose on concrete kernels, but a *uniform*
`ascend_sound` over all of `IsCoveredSU` additionally needs the `RScalarSetExpr` leaf
(the `semLowerSExpr` success guard) and a `Corres`-over-`semScalarWhile` variant for
`RWhileNz` — the same frontier the descent tracks.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-- The assignable straight-line fragment the value leaf covers uniformly:
    `RSkip`/`RBlock`/`RSeq`/`RScalarSet`. -/
inductive IsAscendable : LowCT → Prop
  | rSkip : IsAscendable .RSkip
  | rBlock {body : LowCT} : IsAscendable body → IsAscendable (.RBlock body)
  | rSeq {c₁ c₂ : LowCT} : IsAscendable c₁ → IsAscendable c₂ → IsAscendable (.RSeq c₁ c₂)
  | rScalarSet (name : String) (n : Nat) : IsAscendable (.RScalarSet name n)

/-- The abstract word transformer (the spec) over `ZMod 2^64` for the ascendable
    fragment — the pure image of `semScalar`. -/
def asemW : LowCT → (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64))
  | .RSkip, a => a
  | .RBlock body, a => asemW body a
  | .RSeq c₁ c₂, a => asemW c₂ (asemW c₁ a)
  | .RScalarSet name n, a => fun s => if s = name then (n : ZMod (2 ^ 64)) else a s
  | _, a => a

/-- Total soundness of the ascent over `IsAscendable`: every such program lifts to its
    pure word spec `asemW c` under `SRword`, by structural recursion assembling the
    `corres_*` database. The precondition is `True` — the word abstraction to `ZMod 2^64`
    is unconditional (it *is* the wrapping semantics). -/
theorem ascend_sound {c : LowCT} (h : IsAscendable c) :
    Corres SRword (fun _ => True) (asemW c) c := by
  induction h with
  | rSkip => exact corres_skip SRword
  | rBlock _ ih => exact corres_block SRword ih
  | rSeq _ _ ih₁ ih₂ =>
      have h := corres_seq SRword ih₁ ih₂ (fun _ _ => trivial)
      exact h
  | rScalarSet name n => exact corres_setScalar name n

/-- The `ascend` tactic: synthesize the word spec `asemW c` and close
    `Corres SRword (fun _ => True) (asemW c) c` — proving `IsAscendable` by constructor
    search, then discharging by `ascend_sound`. -/
macro "ascend" : tactic => `(tactic| exact ascend_sound (by repeat' constructor))

/-! ## `ascend` in action + the control rules composing on concrete kernels -/

/-- A straight-line word kernel lifts by one tactic invocation. -/
example : Corres SRword (fun _ => True) (asemW (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)))
    (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)) := by ascend

/-- Nested blocks and sequencing, one `ascend`. -/
example : Corres SRword (fun _ => True)
    (asemW (.RBlock (.RSeq (.RScalarSet "a" 1) (.RSeq (.RScalarSet "b" 2) (.RScalarSet "c" 3)))))
    (.RBlock (.RSeq (.RScalarSet "a" 1) (.RSeq (.RScalarSet "b" 2) (.RScalarSet "c" 3)))) := by
  ascend

/-- The conditional rule composes on a concrete branch kernel (via `corres_if`). -/
example : Corres SRword (fun _ => True)
    (fun a s => if s = "r" then (if a "g" = 0 then (7 : ZMod (2 ^ 64)) else (5 : ZMod (2 ^ 64)))
      else a s)
    (.RIfNz "g" (.RScalarSet "r" 5) (.RScalarSet "r" 7)) :=
  corres_if "g" "r" 5 7

/-! ## The value-leaf transfer via the `param_auto` coordinator

`ascend` integrates the *structural* leaves (`corres_setScalar`/`_seq`/`_block`/`_skip`).
Its arithmetic sibling — the `RScalarSetExpr` value leaf (`Ascent.ExprLeaf`) — rests on a
word-op-tree representation change through the registered `RelatedBinOp wEnc` squares
(`wEncAdd`/`wEncSub`/`wEncMul`, `Ascent.Corres`). Stated relationally, that obligation is
closed uniformly by ParamTransfer's `param_auto` coordinator, which routes it to `rcongr`
(cross-head congruence descent over the *same* `wEnc` squares that `composeBinOp` consumes).
One call site discharges the whole tree, of any op-shape — the tactic-level dual to the
`(inferInstance : Related wEnc …).rel` idiom.

Note: `param_auto` needs the goal in `Related wEnc` form to pick up the encoding; on a bare
`wEnc (t) = t'` equality `rcongr` defaults to `Related id` and cannot descend the squares —
so the value-leaf induction in `ExprLeaf` (bare-equality per node) still names its square. -/

/-- `param_auto` closes a value-leaf word-op tree (mixed `*`/`-`) via `rcongr`, dispatching
    over the registered `wEnc` squares — no explicit `.comm` naming. -/
example (x y z : BitVec 64) :
    Transfer.Related wEnc (x * y - z) (wEnc x * wEnc y - wEnc z) := by param_auto

/-- The equational face of the same value leaf: the coordinator builds the `Related`
    witness, `.rel` reads off the transfer equation `wEnc (t) = t'` the leaf needs. -/
example (x y z : BitVec 64) : wEnc (x * y - z) = wEnc x * wEnc y - wEnc z :=
  (by param_auto : Transfer.Related wEnc (x * y - z) (wEnc x * wEnc y - wEnc z)).rel

end CatCrypt.Crypto.SecureCompilation.Ascent
