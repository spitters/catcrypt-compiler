/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminTranslate
public import CatCrypt.Deep.Eval
public import CatCrypt.Core.Heap

/-!
# Loop Scope of the Jasmin Translation

A function body that writes a variable before a counted loop, updates it inside the
loop and reads it after the loop, translated by `translateFun`. The instruction after
the loop reads the value the loop body wrote, because `Cfor` keeps the scope of its
surroundings (`translateCmd_cfor_newSid`).

## Main results

- `translateFun_countLoop_eval`: the body
  `x := 0; for i in 0..3 { x := x + 1 }; y := x; return y` returns `3`.
- `eval_put_wordLoc`, `eval_put_intLoc`: evaluating a write to a word or integer
  variable location sets the heap at that location.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin

open CatCrypt.Core CatCrypt.Deep CatCrypt.Prob

set_option autoImplicit false

noncomputable section

/-- Evaluating a write to a word variable location sets the heap at that location. -/
theorem eval_put_wordLoc (sid : ScopeId) (v : Var) (ws : WSize)
    (val : (wordLoc sid v ws).ty) (heap : Heap) :
    (RawCode.put (wordLoc sid v ws) val).eval heap =
      SDistr.pure (⟨()⟩, heap.set (wordLoc sid v ws) val) := by
  simp only [CatCrypt.Deep.eval_put, SPComp.bind_def, SPComp.set_def, SPComp.pure_def,
    SDistr.pure_bind]

/-- Evaluating a write to an integer variable location sets the heap at that location. -/
theorem eval_put_intLoc (sid : ScopeId) (v : Var) (val : (intLoc sid v).ty) (heap : Heap) :
    (RawCode.put (intLoc sid v) val).eval heap =
      SDistr.pure (⟨()⟩, heap.set (intLoc sid v) val) := by
  simp only [CatCrypt.Deep.eval_put, SPComp.bind_def, SPComp.set_def, SPComp.pure_def,
    SDistr.pure_bind]

/-- The 64-bit word variable `x` of `countLoopFun`. -/
def countX : Var := { vname := "x", vtype := .sword .U64 }

/-- The integer loop counter `i` of `countLoopFun`. -/
def countI : Var := { vname := "i", vtype := .sint }

/-- The 64-bit word result variable `y` of `countLoopFun`. -/
def countY : Var := { vname := "y", vtype := .sword .U64 }

/-- The 64-bit word constant `z`. -/
def wordConstU64 (z : Int) : PExpr := .Papp1 (.Oword_of_int .U64) (.Pconst z)

/-- The function `x := 0; for i in 0..3 { x := x + 1 }; y := x; return y`. -/
def countLoopFun : FunDecl where
  name := { name := "count" }
  params := []
  body :=
    [ .Cassgn (.Lvar { var := countX }) .AT_none (.sword .U64) (wordConstU64 0),
      .Cfor { var := countI } { dir := .UpTo, lo := 0, hi := 3 }
        [ .Cassgn (.Lvar { var := countX }) .AT_none (.sword .U64)
            (.Papp2 (.Oadd .U64) (.Pvar { gv := { var := countX }, gs := false })
              (wordConstU64 1)) ],
      .Cassgn (.Lvar { var := countY }) .AT_none (.sword .U64)
        (.Pvar { gv := { var := countX }, gs := false }) ]
  results := [{ var := countY }]

/-- The loop counter and `x` occupy distinct heap locations in every scope. -/
theorem countI_id_ne_countX_id (sid : ScopeId) :
    (intLoc sid countI).id ≠ (wordLoc sid countX .U64).id := by
  simp [intLoc, wordLoc, varLocId, countI, countX, Nat.pair_eq_pair, encodeSType, WSize.bits]

/-- `countLoopFun` returns `3` from every heap, in every scope, at fuel `10`. -/
theorem translateFun_countLoop_eval (env : TransEnv) (sid : ScopeId) (heap : Heap) :
    ∃ heap', (translateFun env countLoopFun sid [] 10).eval heap =
      SDistr.pure ([⟨.sword .U64, (3 : BitVec 64)⟩], heap') := by
  simp only [translateFun, translateFun.writeParams, translateFun.readResults, countLoopFun,
    translateCmd, translateInstrR, translateForLoop, loopRange, translatePExpr, readGVar,
    readVar, writeVar, translateWriteLVal, wordConstU64, evalSop1, evalSop2, coerceValue,
    countX, countI, countY, CatCrypt.Deep.eval_bind, CatCrypt.Deep.eval_get,
    CatCrypt.Deep.eval_ret, SPComp.bind_def, SPComp.get_def, SPComp.pure_def, SDistr.pure_bind,
    List.range_succ, List.range_zero, List.map, dite_true, truncateWord, intToWord,
    List.nil_append, List.cons_append, Nat.sub_zero, Nat.add_zero]
  repeat (first
    | erw [Heap.get_set_other _ _ _ _ (countI_id_ne_countX_id sid)]
    | erw [Heap.get_set_same]
    | erw [eval_put_wordLoc]
    | erw [eval_put_intLoc]
    | (erw [SDistr.pure_bind]; dsimp only))
  exact ⟨_, rfl⟩

end

end CatCrypt.Crypto.Jasmin
