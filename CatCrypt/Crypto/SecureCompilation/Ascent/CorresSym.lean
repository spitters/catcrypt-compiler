/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Ascent.CorresX86Mem
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresX86Mem
public import Lean

/-!
# `corres_sym`: a `SymM` worklist solver for `CorresJ` over a straight-line block

`corres_sym` closes a goal `CorresJ SR P fa block` for a straight-line
`List (JInstr 64)` block by composing the `@[corres]` leaves, the same decomposition as
`corres_solve` (`CorresSolver.lean`) and `corres_solve_mem` (`CorresX86Mem.lean`),
run by an engine over `Lean.Meta.Sym`:

* the goal is hash-consed (`Sym.preprocessMVar`) and every target the engine builds is
  re-shared (`Sym.shareCommonInc`);
* the engine is a worklist loop over goals, so the block length bounds the loop count
  and not the recursion depth;
* the `@[corres]` leaves are indexed by the head constant of the state relation and the
  constructor of the instruction, and each leaf is compiled at most once per call into a
  `Sym.BackwardRule`, applied by pattern unification;
* a precondition other than `fun _ => True` is weakened by `corresJ_weaken`, a concrete
  transition is freed to a metavariable by `corresJ_castFa`, and a block `i :: c` splits
  by `corresJ_cons_true`, the head leaf assigning the head step and the tail the rest;
* a side condition of a leaf (a cell membership `(b, o) ∈ cells`, a base-register
  exclusion `d ∉ baseRegs cells`, a carry condition `c ∈ carryConds`) is closed by
  `decide`, with one proof per distinct proposition; a side condition `decide` does not
  close is returned as a goal;
* the synthesized transition is compared with the goal's transition by `isDefEq` at
  default transparency.

A block that is not a list literal is put in weak head normal form at each step, so a
definition such as `solinasSquareBlock`, or a concatenation of segments, needs no
`unfold`.

The engine design (a worklist over hash-consed goals, apply-ready rules cached per
spec, rule application by pattern matching) follows Sebastian Graf's `ascend` engine in
the repository `sgraf812/ascent`.

## Main results

* `corresJ_cons_true`: the cons composition at precondition `fun _ => True`.
* `corres_sym`: the solver.
* `solinasSeg1_corres_sym` … `solinasSeg4_corres_sym`: the four `solinas_square`
  segments over `SRmem solinasCells`, one `corres_sym` call each.
* `solinasSquareBlock_corres_sym`: the 99-instruction `solinas_square` body over
  `SRmem solinasCells`, one `corres_sym` call.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- `corresJ_cons` at precondition `fun _ => True`: a leaf on the head instruction and a
    `CorresJ` on the tail compose to the block `i :: c` with the transitions composed as
    `fun a => ga (fa a)`. -/
theorem corresJ_cons_true {AState : Type} (SR : JState 64 → AState → Prop)
    {fa ga : AState → AState} {i : JInstr 64} {c : List (JInstr 64)}
    (h₁ : CorresJ SR (fun _ => True) fa [i]) (h₂ : CorresJ SR (fun _ => True) ga c) :
    CorresJ SR (fun _ => True) (fun a => ga (fa a)) (i :: c) :=
  corresJ_cons SR h₁ h₂ (fun _ _ => trivial)

namespace CorresSym

meta section

open Lean Meta Elab Tactic Sym

/-- The index key of a leaf: the head constant of the state relation and the constructor
    of the instruction, `Name.anonymous` where the leaf leaves that position open. -/
abbrev LeafKey := Name × Name

/-- The head constant name of `e`, or `Name.anonymous`. -/
def headName (e : Expr) : Name :=
  e.getAppFn.constName?.getD .anonymous

/-- The `@[corres]` leaves, indexed by `LeafKey`. -/
def buildIndex : MetaM (Std.HashMap LeafKey (Array Name)) := do
  let mut idx : Std.HashMap LeafKey (Array Name) := {}
  for name in ← Lean.labelled `corres do
    let info ← getConstInfo name
    let key? ← forallTelescope info.type fun _ concl => do
      unless concl.isAppOfArity ``CorresJ 5 do return none
      let args := concl.getAppArgs
      let blk := args[4]!
      unless blk.isAppOfArity ``List.cons 3 do return none
      return some (headName args[1]!, headName blk.getAppArgs[1]!)
    if let some key := key? then
      idx := idx.insert key ((idx.getD key #[]).push name)
  return idx

/-- The engine state: the leaf index, the compiled rules, the side-condition proofs, the
    goals returned to the caller. -/
structure State where
  /-- The `@[corres]` leaves by key. -/
  index : Std.HashMap LeafKey (Array Name)
  /-- Compiled backward rules by declaration name. -/
  rules : Std.HashMap Name BackwardRule := {}
  /-- `decide` proofs by proposition; `none` records a proposition `decide` did not close. -/
  decided : Std.HashMap Expr (Option Expr) := {}
  /-- Goals returned to the caller. -/
  residual : Array MVarId := #[]

/-- The engine monad. -/
abbrev M := StateRefT State SymM

/-- The backward rule of `name`, compiled on first use. -/
def ruleOf (name : Name) : M BackwardRule := do
  if let some r := (← get).rules[name]? then return r
  let r ← mkBackwardRuleFromDecl name
  modify fun s => { s with rules := s.rules.insert name r }
  return r

/-- Apply `rule` to `goal`, restoring the metavariable context when it does not apply. -/
def tryRule (goal : MVarId) (rule : BackwardRule) : M (Option (List MVarId)) := do
  let saved ← (saveState : MetaM Meta.SavedState)
  match ← rule.apply goal with
  | .goals gs => return some gs
  | .failed => saved.restore; return none

/-- A proof of `p` by `decide`, cached by `p`. -/
def decideCached (p : Expr) : M (Option Expr) := do
  if let some r := (← get).decided[p]? then return r
  let r ← try
      let pf ← mkDecideProof p
      let inst := pf.appFn!.appArg!
      let v ← withAtLeastTransparency .default <| whnf inst
      pure (if v.isAppOf ``Decidable.isTrue then some pf else none)
    catch _ => pure none
  modify fun s => { s with decided := s.decided.insert p r }
  return r

/-- Apply the first indexed leaf for `SR` and instruction `i` that unifies with `goal`. -/
def applyLeaf (goal : MVarId) (sr i : Expr) : M (List MVarId) := do
  let idx := (← get).index
  let k₁ := headName sr
  let k₂ := headName i
  let keys : Array LeafKey := #[(k₁, k₂), (k₁, .anonymous), (.anonymous, k₂),
    (.anonymous, .anonymous)]
  for key in keys do
    for name in idx.getD key #[] do
      if let some gs ← tryRule goal (← ruleOf name) then
        return gs
  throwError "corres_sym: no @[corres] leaf applies to{indentExpr (← goal.getType)}"

/-- One worklist step on `goal`. A `CorresJ` goal is decomposed (a leaf, a cons split, the
    empty block, or the block put in weak head normal form) and its subgoals returned; any
    other goal is closed by `decide` or recorded as residual. -/
def step (goal : MVarId) : M (List MVarId) := goal.withContext do
  let target ← instantiateMVarsIfMVarApp (← goal.getType)
  unless target.isAppOfArity ``CorresJ 5 do
    if let some pf ← decideCached target then
      goal.assign pf
    else
      modify fun s => { s with residual := s.residual.push goal }
    return []
  let args := target.getAppArgs
  let blk := args[4]!
  if blk.isAppOfArity ``List.cons 3 then
    let bargs := blk.getAppArgs
    let tail := bargs[2]!
    if tail.isAppOfArity ``List.nil 1 then
      return ← applyLeaf goal args[1]! bargs[1]!
    let .goals gs ← (← ruleOf ``corresJ_cons_true).apply goal
      | throwError "corres_sym: corresJ_cons_true does not apply to{indentExpr target}"
    return gs
  if blk.isAppOfArity ``List.nil 1 then
    let .goals gs ← (← ruleOf ``corresJ_nil).apply goal
      | throwError "corres_sym: corresJ_nil does not apply to{indentExpr target}"
    return gs
  let blk' ← whnfD blk
  if blk'.isAppOfArity ``List.cons 3 || blk'.isAppOfArity ``List.nil 1 then
    let target' ← shareCommonInc (mkAppN target.getAppFn (args.set! 4 blk'))
    return [← goal.replaceTargetDefEq target']
  throwError "corres_sym: the block is not a list{indentExpr blk}"

/-- Run the worklist from `goal` to exhaustion. -/
def work (goal : MVarId) : M Unit := do
  let mut stack := #[goal]
  while let some g := stack.back? do
    stack := stack.pop
    let gs ← step g
    stack := stack ++ gs.toArray.reverse

/-- Weaken the precondition to `fun _ => True` and free the transition to a metavariable;
    returns the goal for the worklist and the pair (synthesized, stated) transition. -/
def prepare (goal : MVarId) : M (MVarId × Option (Expr × Expr)) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``CorresJ 5 do
    throwError "corres_sym: the goal is not a CorresJ{indentExpr target}"
  let args := target.getAppArgs
  let aTy := args[0]!
  let sr := args[1]!
  let pre := args[2]!
  let fa := args[3]!
  let blk := args[4]!
  let isTruePre := pre.isLambda && pre.bindingBody!.isConstOf ``True
  let truePre ← shareCommonInc (mkLambda `a .default aTy (mkConst ``True))
  let mut goal := goal
  unless isTruePre do
    let g' ← mkFreshExprMVar
      (← shareCommonInc (mkApp5 (mkConst ``CorresJ) aTy sr truePre fa blk))
    let himp ← withLocalDeclD `a aTy fun a => do
      withLocalDeclD `h (mkApp pre a) fun h => mkLambdaFVars #[a, h] (mkConst ``True.intro)
    goal.assign (mkAppN (mkConst ``corresJ_weaken) #[aTy, sr, truePre, pre, fa, blk, g', himp])
    goal := g'.mvarId!
  if (← instantiateMVars fa).getAppFn.isMVar then
    return (goal, none)
  let f ← mkFreshExprMVar (← mkArrow aTy aTy)
  let g' ← mkFreshExprMVar (← shareCommonInc (mkApp5 (mkConst ``CorresJ) aTy sr truePre f blk))
  let he := mkApp2 (mkConst ``Eq.refl [Level.one]) (← mkArrow aTy aTy) fa
  goal.assign (mkAppN (mkConst ``corresJ_castFa) #[aTy, sr, truePre, f, fa, blk, g', he])
  return (g'.mvarId!, some (f, fa))

/-- Run `corres_sym` on `goal`; returns the residual goals. -/
def run (goal : MVarId) : MetaM (List MVarId) := do
  let index ← buildIndex
  SymM.run do
    let goal ← preprocessMVar goal
    let go : M (List MVarId) := do
      let (g, cast?) ← prepare goal
      work g
      if let some (f, fa) := cast? then
        unless ← withAtLeastTransparency .default <| isDefEq f fa do
          throwError "corres_sym: the synthesized transition{indentExpr (← instantiateMVars f)}\n\
            is not definitionally equal to{indentExpr fa}"
      return (← get).residual.toList
    go.run' { index }

/-- Close `CorresJ SR P fa block` over a straight-line block by composing the `@[corres]`
    leaves with the `Lean.Meta.Sym` worklist engine of `CorresSym.run`. Side conditions
    that `decide` does not close are left as goals. -/
elab "corres_sym" : tactic => do
  let rest ← run (← getMainGoal)
  replaceMainGoal rest

end

end CorresSym

open CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasSquareBlock

/-- A dual-carry block over `SRcarry2`, closed by `corres_sym`. -/
theorem corres_sym_adx (dh dl ra rb d1 s1 d2 s2 : String) :
    CorresJ SRcarry2 (fun _ => True)
      (fun a => adoxStep2 d2 s2 (adcxStep2 d1 s1 (mulxStep2 dh dl ra rb a)))
      [.mulx dh dl (.reg ra) (.reg rb), .adcx d1 (.reg s1), .adox d2 (.reg s2)] := by
  corres_sym

/-- Instructions 1–33 of `solinas_square` refine their abstract run over
    `SRmem solinasCells`, by `corres_sym`. -/
theorem solinasSeg1_corres_sym :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSeg1) solinasSeg1 := by
  corres_sym

/-- Instructions 34–65 of `solinas_square` refine their abstract run over
    `SRmem solinasCells`, by `corres_sym`. -/
theorem solinasSeg2_corres_sym :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSeg2) solinasSeg2 := by
  corres_sym

/-- Instructions 66–93 of `solinas_square` refine their abstract run over
    `SRmem solinasCells`, by `corres_sym`. -/
theorem solinasSeg3_corres_sym :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSeg3) solinasSeg3 := by
  corres_sym

/-- Instructions 94–99 of `solinas_square` refine their abstract run over
    `SRmem solinasCells`, by `corres_sym`. -/
theorem solinasSeg4_corres_sym :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSeg4) solinasSeg4 := by
  corres_sym

/-- The 99-instruction `solinas_square` body refines its abstract run over
    `SRmem solinasCells`, by one `corres_sym` call at the default `maxRecDepth`. -/
theorem solinasSquareBlock_corres_sym :
    CorresJ (SRmem solinasCells) (fun _ => True) (absRunMem solinasSquareBlock)
      solinasSquareBlock := by
  corres_sym

end CatCrypt.Crypto.SecureCompilation.Ascent
