/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.CorresSymEngine
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresSymEngine
public import Lean

/-!
# `corres_sym_scalar`: the `SymM` engine at the scalar `Corres`

`Corres SR P fa c` (`Corres`) is the correspondence over `semScalar`. Its composition
rule `corres_seq` has the shape the engine of `CorresSymEngine` composes: a judgment on
`c₁` and one on `c₂` give the judgment on `.RSeq c₁ c₂` with the transitions composed
as `fun a => ga (fa a)`. This module instantiates the engine at that judgment.

* A block `.RSeq c₁ c₂` is composite, `.RSkip` is empty, and any other `LowCT`
  constructor application is a leaf; the engine splits the `RSeq` tree in either
  nesting.
* The leaf is `corres_setExprWord`, the word value leaf over `SRwordBV`. Its side
  condition `srcClean e` states `¬ isTmpName` of the names of `e`, which `decide` does
  not close, so the engine returns it and `corres_sym_scalar` closes it by
  `corres_scalar_clean`.

## Main results

* `corres_seq_true`: `corres_seq` at precondition `fun _ => True`.
* `corresScalarMachine`, `corres_sym_scalar`: the engine instance and its tactic.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-- `corres_seq` at precondition `fun _ => True`: the judgments on `c₁` and `c₂` compose
    to the judgment on `.RSeq c₁ c₂` with the transitions composed as
    `fun a => ga (fa a)`. -/
theorem corres_seq_true {AState : Type} (SR : SEnvScalar → AState → Prop)
    {fa ga : AState → AState} {c₁ c₂ : LowCT}
    (h₁ : Corres SR (fun _ => True) fa c₁) (h₂ : Corres SR (fun _ => True) ga c₂) :
    Corres SR (fun _ => True) (fun a => ga (fa a)) (.RSeq c₁ c₂) :=
  corres_seq SR h₁ h₂ (fun _ _ => trivial)

open Lean Meta in
/-- The shape of a `LowCT` term: `.RSeq` is composite, `.RSkip` empty, any other
    constructor application a leaf. -/
meta def lowCTShape (c : Expr) : MetaM CorresSymEngine.Shape := do
  if c.isAppOfArity ``LowCT.RSeq 2 then return .split
  if c.isConstOf ``LowCT.RSkip then return .empty
  match c.getAppFn.constName? with
  | some n =>
    if (← getEnv).isConstructor n then return .leaf c else return .other
  | none => return .other

/-- The scalar machine of the `SymM` engine: `Corres` over a `LowCT` term, the leaf
    `corres_setExprWord`, `corres_seq_true`, `corres_skip`, `corres_weaken` and
    `corres_castFa`; side conditions are returned to the caller. -/
meta def corresScalarMachine : CorresSymEngine.Machine where
  name := "corres_sym_scalar"
  judgment := ``Corres
  leaves := pure #[``corres_setExprWord]
  split := ``corres_seq_true
  empty := ``corres_skip
  weaken := ``corres_weaken
  castFa := ``corres_castFa
  classify := lowCTShape
  decideSide := false

/-- The engine of `CorresSymEngine` at `corresScalarMachine`, leaving the `srcClean`
    side conditions as goals. -/
elab "corres_sym_scalar_core" : tactic => CorresSymEngine.solve corresScalarMachine

/-- Close `Corres SRwordBV P fa c` over a straight-line `RSeq` / `RScalarSetExpr` tree
    by composing `corres_setExprWord` with the `SymM` engine, and close the `srcClean`
    side conditions by `corres_scalar_clean`. The synthesized transition is matched
    against the goal's transition by definitional equality. -/
macro "corres_sym_scalar" : tactic =>
  `(tactic| (corres_sym_scalar_core <;> corres_scalar_clean))

/-! ## Tests -/

/-- A ChaCha-style `d := d ^^^ a`. -/
example :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = "d" then SExpr.evalBV a (.SXor (.SVar "d") (.SVar "a")) else a s)
      (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a"))) := by
  corres_sym_scalar

/-- A two-statement mix `t := a &&& b; d := t ^^^ c`. -/
example :
    Corres SRwordBV (fun _ => True)
      (fun a => (fun a s => if s = "d" then SExpr.evalBV a (.SXor (.SVar "t") (.SVar "c")) else a s)
        ((fun a s => if s = "t" then SExpr.evalBV a (.SAnd (.SVar "a") (.SVar "b")) else a s) a))
      (.RSeq (.RScalarSetExpr "t" (.SAnd (.SVar "a") (.SVar "b")))
        (.RScalarSetExpr "d" (.SXor (.SVar "t") (.SVar "c")))) := by
  corres_sym_scalar

end CatCrypt.Crypto.SecureCompilation.Ascent
