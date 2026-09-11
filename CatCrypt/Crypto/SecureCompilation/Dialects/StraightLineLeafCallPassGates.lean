/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.StraightLineLeafCallEmit
public import CatCrypt.Crypto.SecureCompilation.Dialects.StraightLineLeafCallEmit

/-!
# Pass-level coverage of `expandCallShadows` (additive; fires exactly on calls)

Sibling of `StraightLineLeafCallEmit` (which holds the render-level shape
gates + emit driver): the pre-RA walk-level gates on `expandCallShadows`.
Kept in its own module — co-locating these gates with the render gates
tripped a `lake`-only mimalloc SIGSEGV in the elaborating `lean` process
(the same content elaborates clean standalone and under the LSP; the
crash is a toolchain allocation-pattern artifact, not a content defect),
and the module boundary dodges the pattern.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.StraightLineLeafCallEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- The body walk (pre-RA) of the mixed program. -/
def leafMixWalk : Lcmd := comToBody 2 argName (fun _ => none) leafMixBody 2

/-- **Fires on a call body:** `expandCallShadows` turns the two `CALL:` shadow
    `Lopn`s into real `LinstrR.Lcall`s (two of them). -/
theorem expandCallShadows_fires :
    ((expandCallShadows leafMixWalk).filter
      (fun i => match i.li_i with | .Lcall _ _ => true | _ => false)).length = 2 := by
  native_decide

/-- **No `CALL:`/`CALLN:` shadow survives** the expansion. -/
theorem expandCallShadows_no_shadow :
    (expandCallShadows leafMixWalk).all (fun i =>
      match i.li_i with
      | .Lopn _ opn _ => !(opn.startsWith "CALL:") && !(opn.startsWith "CALLN:")
      | _ => true) = true := by native_decide

/-- A call-free straight-line body `g(a0,a1) = a0 ⊕ a1`. -/
def leafFreeBody : Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .var (.mk (.regArith .xor 64) rfl (.cons .here (.cons (.there .here) .nil)))
  (.ret .here)

/-- **Additive:** on a call-free body `expandCallShadows` is the identity, so the
    straight-line export is byte-identical to the pre-call-arm behaviour. -/
theorem expandCallShadows_id_on_callfree :
    (expandCallShadows (comToBody 2 argName (fun _ => none) leafFreeBody 2)).map
        (fun i => i.li_i.toText)
      = (comToBody 2 argName (fun _ => none) leafFreeBody 2).map
        (fun i => i.li_i.toText) := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.StraightLineLeafCallEmit
