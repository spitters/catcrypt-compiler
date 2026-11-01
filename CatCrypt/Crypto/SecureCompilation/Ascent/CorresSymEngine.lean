/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean
public meta import Lean

/-!
# A `SymM` worklist engine for the ascent's correspondence judgments

The engine closes a goal `J SR P fa block`, where `J` is a correspondence judgment of
the ascent (`CorresJ` over `runBlock`, `CorresR` over `runRBlock64`, `Corres` over
`semScalar`), by composing the per-instruction leaves of `J` over a straight-line
block. It runs in `Lean.Meta.Sym`:

* the goal is hash-consed (`Sym.preprocessMVar`) and every target the engine builds is
  re-shared (`Sym.shareCommonInc`);
* the engine is a worklist loop over goals, so the block length bounds the loop count
  and not the recursion depth;
* the leaves are the machine's leaf declarations, indexed by the head
  constant of the state relation and the head constant of the instruction, and each
  leaf is compiled at most once per call into a `Sym.BackwardRule`, applied by pattern
  unification;
* a precondition other than `fun _ => True` is weakened by the machine's weakening
  lemma, a concrete transition is freed to a metavariable by the machine's cast lemma,
  and a composite block is split by the machine's composition lemma;
* a side condition of a leaf is closed by `decide`, with one proof per distinct
  proposition, when the machine enables it; a side condition not closed is returned as
  a goal;
* the synthesized transition is compared with the goal's transition by `isDefEq` at
  default transparency.

A block that the machine does not classify is put in weak head normal form, and so is
an instruction whose head is not a constructor, so a block given as a definition, a
concatenation or a translation `xs.map f` needs no unfolding by the caller.

## The machine description

A `Machine` fixes

* `judgment`: the judgment constant, applied to five arguments
  `(AState, SR, P, fa, block)` and without universe parameters;
* `leaves`: the leaf declarations (for a label attribute `attr`, `Lean.labelled attr`),
  each with conclusion `judgment AState SR (fun _ => True) step block` for a `block`
  classified as a leaf;
* `split`: a lemma concluding the judgment at precondition `fun _ => True` on a
  composite block, with the transitions composed;
* `empty`: a lemma concluding the judgment on the empty block;
* `weaken`: a lemma with explicit arguments `(AState, SR, P, P', fa, block, h, himp)`
  concluding the judgment at `P'` from the judgment at `P` and `∀ a, P' a → P a`;
* `castFa`: a lemma with explicit arguments `(AState, SR, P, fa, fa', block, h, he)`
  concluding the judgment at `fa'` from the judgment at `fa` and `fa = fa'`;
* `classify`: the shape of a block (`Shape.leaf i`, `Shape.split`, `Shape.empty`, or
  `Shape.other`);
* `decideSide`: whether side conditions are tried by `decide`.

`listShape` is the classifier of a block given as a `List` of instructions: a
singleton is a leaf, a longer cons is composite, `[]` is empty. An instance is a
`Machine` value; `solve` runs the engine on the main goal, and a tactic is
`elab "name" : tactic => CorresSymEngine.solve machine`.

The engine design (a worklist over hash-consed goals, apply-ready rules cached per
spec, rule application by pattern matching) follows Sebastian Graf's `ascend` engine in
the repository `sgraf812/ascent`.

## Main definitions

* `Shape`, `Machine`, `listShape`: the machine description.
* `run`: the engine on one goal, returning the goals it leaves.
* `solve`: the engine on the main goal of a tactic.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.CorresSymEngine

meta section

open Lean Meta Elab Tactic Sym

/-- The shape of a block: a single instruction `i`, a composite block, the empty block,
    or a term to be put in weak head normal form. -/
inductive Shape where
  /-- A single instruction. -/
  | leaf (instr : Expr)
  /-- A block split by the machine's composition lemma. -/
  | split
  /-- The empty block. -/
  | empty
  /-- A term that is none of the above. -/
  | other

/-- A correspondence judgment and the lemmas the engine composes it with. -/
structure Machine where
  /-- The name used in error messages. -/
  name : String
  /-- The judgment constant, of arity five: `(AState, SR, P, fa, block)`. -/
  judgment : Name
  /-- The leaf declarations, usually `Lean.labelled` of a label attribute. -/
  leaves : MetaM (Array Name)
  /-- The composition lemma on a composite block at precondition `fun _ => True`. -/
  split : Name
  /-- The lemma on the empty block. -/
  empty : Name
  /-- The precondition weakening lemma. -/
  weaken : Name
  /-- The transition rewriting lemma. -/
  castFa : Name
  /-- The shape of a block. -/
  classify : Expr → MetaM Shape
  /-- Whether side conditions are tried by `decide`. -/
  decideSide : Bool := true

/-- The shape of a block given as a `List`: `[i]` is a leaf, `i :: c` otherwise
    composite, `[]` empty. -/
def listShape (blk : Expr) : MetaM Shape :=
  pure <|
    if blk.isAppOfArity ``List.cons 3 then
      if blk.appArg!.isAppOfArity ``List.nil 1 then .leaf blk.appFn!.appArg! else .split
    else if blk.isAppOfArity ``List.nil 1 then .empty
    else .other

/-- The index key of a leaf: the head constant of the state relation and of the
    instruction, `Name.anonymous` where the leaf leaves that position open. -/
abbrev LeafKey := Name × Name

/-- The head constant name of `e`, or `Name.anonymous`. -/
def headName (e : Expr) : Name :=
  e.getAppFn.constName?.getD .anonymous

/-- The leaves of `m`, indexed by `LeafKey`. -/
def buildIndex (m : Machine) : MetaM (Std.HashMap LeafKey (Array Name)) := do
  let mut idx : Std.HashMap LeafKey (Array Name) := {}
  for name in ← m.leaves do
    let info ← getConstInfo name
    let key? ← forallTelescope info.type fun _ concl => do
      unless concl.isAppOfArity m.judgment 5 do return none
      let args := concl.getAppArgs
      match ← m.classify args[4]! with
      | .leaf i => return some (headName args[1]!, headName i)
      | _ => return none
    if let some key := key? then
      idx := idx.insert key ((idx.getD key #[]).push name)
  return idx

/-- The engine state: the leaf index, the compiled rules, the side-condition proofs, the
    goals returned to the caller. -/
structure State where
  /-- The leaves by key. -/
  index : Std.HashMap LeafKey (Array Name)
  /-- Compiled backward rules by declaration name. -/
  rules : Std.HashMap Name BackwardRule := {}
  /-- `decide` proofs by proposition; `none` records a proposition `decide` did not close. -/
  decided : Std.HashMap Expr (Option Expr) := {}
  /-- Goals returned to the caller. -/
  residual : Array MVarId := #[]

/-- The engine monad. -/
abbrev M := ReaderT Machine (StateRefT State SymM)

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

/-- Apply the rule `name` to `goal`, failing with an error when it does not apply. -/
def applyNamed (goal : MVarId) (name : Name) (target : Expr) : M (List MVarId) := do
  let .goals gs ← (← ruleOf name).apply goal
    | throwError "{(← read).name}: {name} does not apply to{indentExpr target}"
  return gs

/-- A proof `of_decide_eq_true p inst rfl` of `p`, cached by `p`, where the kernel puts
    `Decidable.decide p inst` in weak head normal form and obtains `true`. The kernel
    evaluates `String` and `Char` equality, which `Meta.whnf` leaves stuck; a `p` with
    metavariables is not decided. -/
def decideCached (p : Expr) : M (Option Expr) := do
  if let some r := (← get).decided[p]? then return r
  let r ← try
      let p ← instantiateMVars p
      if p.hasMVar then pure none else
      let pf ← mkDecideProof p
      let inst := pf.appFn!.appArg!
      let dec := mkApp2 (mkConst ``Decidable.decide) p inst
      let v ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) dec)
      pure (if v.isConstOf ``Bool.true then some pf else none)
    catch _ => pure none
  modify fun s => { s with decided := s.decided.insert p r }
  return r

/-- Apply the first indexed leaf for `SR` and instruction `i` that unifies with `goal`. -/
def tryLeaves (goal : MVarId) (sr i : Expr) : M (Option (List MVarId)) := do
  let idx := (← get).index
  let k₁ := headName sr
  let k₂ := headName i
  let keys : Array LeafKey := #[(k₁, k₂), (k₁, .anonymous), (.anonymous, k₂),
    (.anonymous, .anonymous)]
  for key in keys do
    for name in idx.getD key #[] do
      if let some gs ← tryRule goal (← ruleOf name) then
        return some gs
  return none

/-- Apply a leaf to the single-instruction goal `goal` with target `target`, block `blk`
    and instruction `i`. When no leaf applies and `i` is not in weak head normal form,
    the goal is returned with `i` replaced by its weak head normal form. -/
def applyLeaf (goal : MVarId) (target blk i : Expr) : M (List MVarId) := do
  let args := target.getAppArgs
  if let some gs ← tryLeaves goal args[1]! i then
    return gs
  let i' ← whnfD i
  if i' == i then
    throwError "{(← read).name}: no leaf applies to{indentExpr target}"
  let blk' := blk.replace fun e => if e == i then some i' else none
  let target' ← shareCommonInc (mkAppN target.getAppFn (args.set! 4 blk'))
  return [← goal.replaceTargetDefEq target']

/-- One worklist step on `goal`. A judgment goal is decomposed (a leaf, a split, the
    empty block, or the block put in weak head normal form) and its subgoals returned;
    any other goal is closed by `decide` or recorded as residual. -/
def step (goal : MVarId) : M (List MVarId) := goal.withContext do
  let m ← read
  let target ← instantiateMVarsIfMVarApp (← goal.getType)
  unless target.isAppOfArity m.judgment 5 do
    if m.decideSide then
      if let some pf ← decideCached target then
        goal.assign pf
        return []
    modify fun s => { s with residual := s.residual.push goal }
    return []
  let args := target.getAppArgs
  let blk := args[4]!
  match ← m.classify blk with
  | .leaf i => applyLeaf goal target blk i
  | .split => applyNamed goal m.split target
  | .empty => applyNamed goal m.empty target
  | .other =>
    let blk' ← whnfD blk
    if let .other ← m.classify blk' then
      throwError "{m.name}: the block is not in the machine's block form{indentExpr blk}"
    let target' ← shareCommonInc (mkAppN target.getAppFn (args.set! 4 blk'))
    return [← goal.replaceTargetDefEq target']

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
  let m ← read
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity m.judgment 5 do
    throwError "{m.name}: the goal is not a {m.judgment}{indentExpr target}"
  let judg := target.getAppFn
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
    let g' ← mkFreshExprMVar (← shareCommonInc (mkApp5 judg aTy sr truePre fa blk))
    let himp ← withLocalDeclD `a aTy fun a => do
      withLocalDeclD `h (mkApp pre a) fun h => mkLambdaFVars #[a, h] (mkConst ``True.intro)
    goal.assign (mkAppN (mkConst m.weaken) #[aTy, sr, truePre, pre, fa, blk, g', himp])
    goal := g'.mvarId!
  if (← instantiateMVars fa).getAppFn.isMVar then
    return (goal, none)
  let f ← mkFreshExprMVar (← mkArrow aTy aTy)
  let g' ← mkFreshExprMVar (← shareCommonInc (mkApp5 judg aTy sr truePre f blk))
  let he := mkApp2 (mkConst ``Eq.refl [Level.one]) (← mkArrow aTy aTy) fa
  goal.assign (mkAppN (mkConst m.castFa) #[aTy, sr, truePre, f, fa, blk, g', he])
  return (g'.mvarId!, some (f, fa))

/-- Run the engine of `m` on `goal`; returns the residual goals. -/
def run (m : Machine) (goal : MVarId) : MetaM (List MVarId) := do
  let index ← buildIndex m
  SymM.run do
    let goal ← preprocessMVar goal
    let go : M (List MVarId) := do
      let (g, cast?) ← prepare goal
      work g
      if let some (f, fa) := cast? then
        unless ← withAtLeastTransparency .default <| isDefEq f fa do
          throwError "{m.name}: the synthesized transition{indentExpr (← instantiateMVars f)}\n\
            is not definitionally equal to{indentExpr fa}"
      return (← get).residual.toList
    (go.run m).run' { index }

/-- Run the engine of `m` on the main goal, replacing it by the residual goals. -/
def solve (m : Machine) : TacticM Unit := do
  let rest ← run m (← getMainGoal)
  replaceMainGoal rest

end

end CatCrypt.Crypto.SecureCompilation.Ascent.CorresSymEngine
