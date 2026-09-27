/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.GenRules
public meta import Lean

/-!
# The surface generator

`Hax.Ascent.Gen.ascendFn` takes the `ImpExpr` literal of a function, its builtin table, the
leaf lemmas of the table and the printed surface function, and returns a shallow Lean
function `f` together with its correspondence theorem `FnCorres bi e entry G f`, or
`FnCorresX` of an `Except` function when the literal returns early.

## Symbolic evaluation

The literal is evaluated symbolically over a binding list (`SEnv`) whose values are
`Value` terms and, when their type is known, the term they encode (`SVal`). Each step
applies one rule of `CatCrypt/Hax/Ascent/GenRules.lean` or `CatCrypt/Hax/Ascent/AscendHax.lean`
with every value and binding list given explicitly (`RApp`), so each premise is a
sub-derivation or a closed side condition:

* a lookup `bindLookup l x = some v`, proved by `rfl`, or through a conditional list by
  `bindLookup_ite_of`;
* a `BindsSub` over explicit lists, proved entry by entry;
* an equation between values, proved by `rfl`, `ite_same`, `ite_enc` or a lemma that selects
  a branch from an exit hypothesis;
* a decidable proposition, proved by `decide` when `whnf` evaluates it and by the kernel
  otherwise (`Kernel.isDefEq`);
* a call `bi f vs = some v`, proved by the first leaf lemma of `f` whose left side matches
  (`matchLeaf`), by the width-family lemmas for a tagged name (`matchTagged`), or by
  `array_lit_enc` (`matchArrayLit`);
* the termination of a `whileFold`, proved from a measure `(y - x).toNat` read off the
  comparisons of the loop (`proveTerm`).

The comparisons of two values that decide how a proof is built (the equal branches of a
conditional, `ite_same`, the branch-selecting lemmas, and the oracle equation) are made at
reducible transparency and then at default transparency within a twentieth of the
heartbeat budget (`isDefEqBounded`); a comparison that exceeds it counts as unequal, so
two branches are merged into a conditional value instead of being unfolded.

A step that finds no rule or cannot close a side condition fails with a message whose
first word names the cause: `construct:`, `leaf:`, `type:`, `unbound:`, `loop:` or `side:`.
No goal is returned: the generator either proves the correspondence or fails.

## Loops

A loop's accumulator is the tuple, in binding order, of the variables its body assigns
among those bound before it; its invariant binds them to the components of the
accumulator and every other variable to its value before the loop. The body is evaluated
over a state extended by the index and the accumulator, and its exit bindings give the
step function. No loop specification is written by hand.

## Types

The type of a binding is the type of the leaf result that produces it. When a leaf is
polymorphic in its result (`new []`, `None`), the type of the surface `let` of the same
name decides it (`GCtx.hints`); parameter types come from the surface signature.

## The oracle

The generated function is compared with the printed surface function by definitional
equality at default transparency (`FnResult.oracle`).

## Main definitions

* `SVal`, `SEnv`, `StCtx`, `GCtx`, `GenM`, `GRes`
* `gen` — the derivation of one literal
* `FnSpec`, `FnResult`, `ascendFn` — the generator on one function
* `runtimeLeaves`, `indexLeaves`, `moduleConsts`
-/

@[expose] public section

meta section

open Lean Meta Elab
open Lean.Elab.Term (TermElabM)

namespace Hax.Ascent.Gen

/-- A value of the symbolic environment: its `Value` term and, for a typed value, the
    type and the term whose encoding it is. -/
structure SVal where
  /-- The `Value` term. -/
  val : Expr
  /-- The type of the encoded term. -/
  ty? : Option Expr := none
  /-- The encoded term. -/
  tm? : Option Expr := none
  deriving Inhabited

/-- A symbolic binding list, the head shadowing the tail. -/
abbrev SEnv := List (String × SVal)

/-- The type `String × Value`. -/
def bpTy : Expr :=
  mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``Hax.Value)

/-- The pair `(k, v)` of a binding. -/
def mkPair (k : String) (v : Expr) : Expr :=
  mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``Hax.Value)
    (mkStrLit k) v

/-- The binding list term of a symbolic binding list. -/
def mkBList (env : SEnv) : Expr :=
  env.foldr (fun p acc => mkApp3 (mkConst ``List.cons [Level.zero]) bpTy (mkPair p.1 p.2.val) acc)
    (mkApp (mkConst ``List.nil [Level.zero]) bpTy)

/-- The encoding `enc tm` at type `ty`. -/
def mkEnc (ty tm : Expr) : MetaM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``Hax.Ascent.HaxEnc) ty)
  return mkApp3 (mkConst ``Hax.Ascent.HaxEnc.enc) ty inst tm

/-- A typed symbolic value. -/
def typedV (ty tm : Expr) : MetaM SVal := do
  return { val := ← mkEnc ty tm, ty? := some ty, tm? := some tm }

/-- The unit value. -/
def unitV : MetaM SVal := typedV (mkConst ``Unit) (mkConst ``Unit.unit)

def intTy : Expr := mkConst ``Int
def boolTy : Expr := mkConst ``Bool

/-- The first binding of every name. -/
def dedupEnv : SEnv → List String → SEnv
  | [], _ => []
  | (k, v) :: r, seen =>
    if seen.contains k then dedupEnv r seen else (k, v) :: dedupEnv r (k :: seen)

/-- The value bound to `x`. -/
def lookupEnv (env : SEnv) (x : String) : Option SVal := (env.find? (·.1 == x)).map (·.2)

/-- The string of a string literal. -/
def strOf? (e : Expr) : Option String :=
  match e with
  | .lit (.strVal s) => some s
  | _ => none

/-- A bounded rendering of a term for error messages: its head and depth. -/
def shortExpr (e : Expr) : MessageData :=
  let head := match e.getAppFn with
    | .const n _ => toString n
    | .fvar _ => "a variable"
    | .lam .. => "a function"
    | _ => "a term"
  m!" {head} applied to {e.getAppNumArgs} arguments, depth {e.approxDepth}"

/-- The first 300 characters of an error. -/
def msgStr (ex : Exception) : MetaM String := do
  let s ← ex.toMessageData.toString
  return String.ofList (s.toList.take 300)

/-- The binder names of a `∀` telescope. -/
partial def binderNamesOf : Expr → Array Name
  | .forallE n _ b _ => #[n] ++ binderNamesOf b
  | _ => #[]

/-- The elements of a list literal. -/
partial def listElems? (e : Expr) : MetaM (Option (List Expr)) := do
  let e ← whnfR (← instantiateMVars e)
  match e.getAppFnArgs with
  | (``List.cons, #[_, h, t]) => return (← listElems? t).map (h :: ·)
  | (``List.nil, #[_]) => return some []
  | _ => return none

/-- `if b = true then t else e`. -/
def mkIteB (b t e : Expr) : MetaM Expr := do
  mkAppM ``ite #[← mkEq b (mkConst ``Bool.true), t, e]

/-- The right-nested product of the types, `Unit` for none. -/
def mkProdTy : List Expr → MetaM Expr
  | [] => return mkConst ``Unit
  | [t] => return t
  | t :: ts => do mkAppM ``Prod #[t, ← mkProdTy ts]

/-- The right-nested tuple of the terms. -/
def mkTuple : List Expr → MetaM Expr
  | [] => return mkConst ``Unit.unit
  | [t] => return t
  | t :: ts => do mkAppM ``Prod.mk #[t, ← mkTuple ts]

/-- The components of a right-nested tuple of `n` components. -/
def tupleComps (x : Expr) : Nat → MetaM (List Expr)
  | 0 => return []
  | 1 => return [x]
  | n + 2 => do
    let rest ← tupleComps (← mkAppM ``Prod.snd #[x]) (n + 1)
    return (← mkAppM ``Prod.fst #[x]) :: rest

/-- The type is a product. -/
def isProdTy (ty : Expr) : MetaM Bool := do
  return (← whnfR ty).isAppOfArity ``Prod 2

/-- Decide a proposition by evaluation, with `whnf` or with the kernel. -/
def proveDecide (p : Expr) : MetaM Expr := do
  let d ← mkDecide p
  let r ← withAtLeastTransparency .default <| whnf d
  if r.isConstOf ``Bool.true then return ← mkDecideProof p
  let p ← instantiateMVars p
  if p.hasExprMVar then throwError "side: cannot decide{shortExpr p}"
  let ok := match Kernel.isDefEq (← getEnv) (← getLCtx) d (mkConst ``Bool.true) with
    | .ok b => b
    | .error _ => false
  unless ok do throwError "side: cannot decide{shortExpr p}"
  mkDecideProof p

/-- Run `x` within a twentieth of the heartbeat budget, counted from its start: `none`
    when `x` throws or exceeds that budget, with the state restored. -/
def boundedTry? {α : Type} (x : MetaM α) : MetaM (Option α) := do
  let s ← saveState
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context
      (fun c => { c with maxHeartbeats := c.maxHeartbeats / 20 }) <| some <$> x)
    fun _ => do s.restore; return none

/-- Whether `a` and `b` are definitionally equal: first at reducible transparency, then at
    the ambient transparency within a twentieth of the heartbeat budget. A check that
    exceeds that budget answers `false`. -/
def isDefEqBounded (a b : Expr) : MetaM Bool := do
  if ← withReducible (isDefEq a b) then return true
  return (← boundedTry? (isDefEq a b)).getD false

/-- A proof `rfl` of `lhs = rhs` that the kernel accepts. -/
def kernelRefl (p : Expr) : MetaM Expr := do
  let p ← instantiateMVars p
  let some (_, lhs, rhs) := p.eq? | throwError "side: not an equation"
  if p.hasExprMVar then throwError "side: open equation"
  let ok := match Kernel.isDefEq (← getEnv) (← getLCtx) lhs rhs with
    | .ok b => b
    | .error _ => false
  unless ok do throwError "side: not definitionally equal"
  mkExpectedTypeHint (← mkEqRefl lhs) p

/-! ### Side conditions -/

/-- The value a binding list assigns to `x`, read syntactically; a conditional list gives
    the conditional of the two values. -/
partial def lookupExpr (l : Expr) (x : String) : MetaM (Option Expr) := do
  let l ← whnfR (← instantiateMVars l)
  match l.getAppFnArgs with
  | (``List.cons, #[_, h, t]) =>
    let h ← whnfR h
    match h.getAppFnArgs with
    | (``Prod.mk, #[_, _, k, v]) =>
      match strOf? (← instantiateMVars k) with
      | some s => if s == x then return some v else lookupExpr t x
      | none => return none
    | _ => return none
  | (``ite, #[_, c, _, l1, l2]) =>
    let some b := c.eq?.map (·.2.1) | return none
    let some v1 ← lookupExpr l1 x | return none
    let some v2 ← lookupExpr l2 x | return none
    return some (← mkIteB b v1 v2)
  | _ => return none

/-- A proof of `(if b = true then v₁ else v₂) = v`. -/
def proveIteEq (b v1 v2 v : Expr) (hyps : Array Expr) : MetaM Expr := do
  let lhs ← mkIteB b v1 v2
  let goal ← mkEq lhs v
  if ← isDefEqBounded lhs v then return ← mkExpectedTypeHint (← mkEqRefl v) goal
  let cands : List (MetaM Expr) :=
    [ (do
        unless ← isDefEqBounded v1 v2 do throwError "no"
        mkAppM ``Hax.Ascent.ite_same #[b, v1]),
      (do
        let (``Hax.Ascent.HaxEnc.enc, #[_, _, t]) := v1.getAppFnArgs | throwError "no"
        let (``Hax.Ascent.HaxEnc.enc, #[_, _, u]) := v2.getAppFnArgs | throwError "no"
        mkAppM ``Hax.Ascent.ite_enc #[b, t, u]) ] ++
    (hyps.toList.map fun h => mkAppM ``Hax.Ascent.ite_of_left_exit #[v1, v2, h]) ++
    (hyps.toList.map fun h => mkAppM ``Hax.Ascent.ite_of_right_exit #[v1, v2, h]) ++
    (hyps.toList.map fun h => mkAppM ``Hax.Ascent.ite_of_left_noexit #[v1, v2, h]) ++
    (hyps.toList.map fun h => mkAppM ``Hax.Ascent.ite_of_right_noexit #[v1, v2, h])
  for c in cands do
    let s ← saveState
    let r ← boundedTry? do
      let pf ← c
      if ← isDefEq (← inferType pf) goal then return some pf else return none
    if let some (some pf) := r then return pf
    s.restore
  throwError "side: cannot prove{shortExpr goal}"

/-- A proof of `bindLookup l x = some v`. -/
partial def proveLookup (l : Expr) (x : String) (v : Expr) (hyps : Array Expr) : MetaM Expr := do
  let l' ← whnfR (← instantiateMVars l)
  if l'.isAppOfArity ``ite 5 then
    let args := l'.getAppArgs
    let some b := args[1]!.eq?.map (·.2.1) | throwError "side: condition of{shortExpr l'}"
    -- a hypothesis that selects one branch
    for h in hyps do
      for (lem, bi) in [(``Hax.Ascent.ite_of_left_exit, 4), (``Hax.Ascent.ite_of_right_exit, 3),
          (``Hax.Ascent.ite_of_left_noexit, 4), (``Hax.Ascent.ite_of_right_noexit, 3)] do
        let s ← saveState
        try
          let eqPf ← mkAppM lem #[args[3]!, args[4]!, h]
          let sub := args[bi]!
          let pf ← proveLookup sub x v hyps
          let r ← mkEqNDRec' eqPf pf x
          return r
        catch _ => s.restore
    let some v1 ← lookupExpr args[3]! x | throwError "side: {x} unbound in a branch"
    let some v2 ← lookupExpr args[4]! x | throwError "side: {x} unbound in a branch"
    let h1 ← proveLookup args[3]! x v1 hyps
    let h2 ← proveLookup args[4]! x v2 hyps
    let h ← proveIteEq b v1 v2 v hyps
    return ← mkAppM ``Hax.Ascent.bindLookup_ite_of #[h1, h2, h]
  let lhs := mkApp2 (mkConst ``Hax.Ascent.bindLookup) l (mkStrLit x)
  let rhs ← mkAppM ``Option.some #[v]
  unless ← isDefEq lhs rhs do throwError "side: {x} is not bound to{shortExpr v}"
  mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq lhs rhs)
where
  /-- From `h : ite c a₁ a₂ = a` and a proof about `a`, the proof about the conditional
      list. -/
  mkEqNDRec' (eqPf pf : Expr) (x : String) : MetaM Expr := do
    let some (_, lhsL, _) := (← inferType eqPf).eq? | throwError "no"
    let motive ← withLocalDeclD `L (← inferType lhsL) fun L => do
      let pty ← inferType pf
      let some (_, _, r) := pty.eq? | throwError "no"
      mkLambdaFVars #[L] (← mkEq (mkApp2 (mkConst ``Hax.Ascent.bindLookup) L (mkStrLit x)) r)
    mkEqNDRec motive pf (← mkEqSymm eqPf)

/-- A proof of `BindsSub l m` for an explicit list `m`. -/
partial def proveBindsSub (l m : Expr) (hyps : Array Expr) : MetaM Expr := do
  let m' ← whnfR (← instantiateMVars m)
  match m'.getAppFnArgs with
  | (``List.nil, _) => mkAppM ``Hax.Ascent.bindsSub_nil_intro #[l]
  | (``List.cons, #[_, h, t]) =>
    let h ← whnfR h
    let (``Prod.mk, #[_, _, k, v]) := h.getAppFnArgs | throwError "side: binding{shortExpr h}"
    let some x := strOf? (← instantiateMVars k) | throwError "side: binding name{shortExpr k}"
    let pl ← proveLookup l x v hyps
    let ps ← proveBindsSub l t hyps
    mkAppM ``Hax.Ascent.bindsSub_cons_intro #[pl, ps]
  | _ => throwError "side: binding list{shortExpr m'}"

/-- A proof of a side condition, with the hypotheses of its telescope. -/
partial def closeProp (p : Expr) (hyps : Array Expr) : MetaM Expr := do
  let p := (← instantiateMVars p).headBeta
  match p.getAppFnArgs with
  | (``Hax.Ascent.BindsSub, #[l, m]) =>
    let pf ← proveBindsSub l m hyps
    mkExpectedTypeHint pf p
  | (``True, #[]) => return mkConst ``True.intro
  | (``_root_.Eq, #[_, lhs, rhs]) =>
    if let (``Hax.Ascent.bindLookup, #[l, x]) := lhs.getAppFnArgs then
      if let some s := strOf? (← instantiateMVars x) then
        if let (``Option.some, #[_, v]) := rhs.getAppFnArgs then
          return ← mkExpectedTypeHint (← proveLookup l s v hyps) p
    if ← isDefEq lhs rhs then
      return ← mkExpectedTypeHint (← mkEqRefl lhs) p
    if let (``Hax.Value.isControlFlow, #[v]) := lhs.getAppFnArgs then
      let v ← instantiateMVars v
      match v.getAppFnArgs with
      | (``Hax.Ascent.cfVal, #[_, _, _, r]) =>
        return ← mkExpectedTypeHint (← mkAppM ``Hax.Ascent.cfVal_isControlFlow #[r]) p
      | (``Hax.Ascent.HaxEnc.enc, #[_, _, t]) =>
        return ← mkExpectedTypeHint (← mkAppM ``Hax.Ascent.HaxEnc.Plain.not_cf #[t]) p
      | (``Hax.Ascent.rangeVal, #[lo, hi]) =>
        return ← mkExpectedTypeHint (← mkAppM ``Hax.Ascent.rangeVal_isControlFlow #[lo, hi]) p
      | _ => pure ()
    if lhs.isAppOfArity ``ite 5 then
      let args := lhs.getAppArgs
      if let some b := args[1]!.eq?.map (·.2.1) then
        return ← mkExpectedTypeHint (← proveIteEq b args[3]! args[4]! rhs hyps) p
    try mkExpectedTypeHint (← proveDecide p) p
    catch _ =>
      try kernelRefl p
      catch _ => throwError "side: cannot prove{shortExpr p}"
  | (fn, args) =>
    try mkExpectedTypeHint (← proveDecide p) p
    catch _ => throwError "side: cannot prove{shortExpr p}\nhead {fn} with {args.size} arguments"

/-- A proof of a side condition `∀ xs, P`. -/
def closeSide (ty : Expr) : MetaM Expr := do
  forallTelescope (← instantiateMVars ty) fun xs body => do
    let pf ← closeProp body xs
    mkLambdaFVars xs pf

/-! ### Rule application -/

/-- A rule instantiated with metavariables. -/
structure RApp where
  /-- The rule. -/
  rule : Name
  /-- The rule constant. -/
  c : Expr
  /-- The metavariables of its binders. -/
  mvs : Array Expr
  /-- The binder infos. -/
  bis : Array BinderInfo
  /-- The binder names. -/
  names : Array Name

/-- Instantiate a rule. -/
def rapp (rule : Name) : MetaM RApp := do
  let c ← mkConstWithFreshMVarLevels rule
  let ty ← inferType c
  let (mvs, bis, _) ← forallMetaTelescope ty
  return { rule, c, mvs, bis, names := binderNamesOf ty }

/-- The metavariable of a binder. -/
def RApp.arg (r : RApp) (n : Name) : MetaM Expr := do
  match r.names.findIdx? (· == n) with
  | some i => return r.mvs[i]!
  | none => throwError "hax_ascend: internal: {r.rule} has no binder {n}"

/-- Assign a binder. -/
def RApp.set (r : RApp) (n : Name) (v : Expr) : MetaM Unit := do
  let m ← r.arg n
  unless ← isDefEq m v do
    throwError "hax_ascend: internal: {r.rule}.{n} does not fit{shortExpr v}\n:{shortExpr (← inferType v)}\nexpected{shortExpr (← instantiateMVars (← inferType m))}"

/-- Close a side condition binder. -/
def RApp.side (r : RApp) (n : Name) : MetaM Unit := do
  let m ← instantiateMVars (← r.arg n)
  unless m.isMVar do return
  let ty ← instantiateMVars (← inferType m)
  let pf ← try closeSide ty catch ex =>
    throwError "{ex.toMessageData}\n(in {r.rule}.{n})"
  unless ← isDefEq m pf do throwError "side: {r.rule}.{n}{shortExpr ty}"

/-- The type of a binder. -/
def RApp.goal (r : RApp) (n : Name) : MetaM Expr := do
  instantiateMVars (← inferType (← r.arg n))

/-- The instantiated rule, with its instances synthesized. -/
def RApp.done (r : RApp) : MetaM Expr := do
  for m in r.mvs, b in r.bis do
    if b.isInstImplicit then
      let m' ← instantiateMVars m
      if m'.isMVar then
        let inst ← synthInstance (← inferType m')
        unless ← isDefEq m' inst do throwError "hax_ascend: internal: instance of {r.rule}"
  let e ← instantiateMVars (mkAppN r.c r.mvs)
  if e.hasExprMVar then
    throwError "hax_ascend: internal: {r.rule} has unassigned arguments{shortExpr e}"
  return e

/-! ### Contexts -/

/-- The abstract state of a derivation: its type, the free variables it binds, their
    readings from one state value, and the state value built from the variables. -/
structure StCtx where
  /-- The state type. -/
  stTy : Expr
  /-- The free variables of the state. -/
  vars : Array Expr
  /-- Their readings from a state value. -/
  proj : Expr → MetaM (Array Expr)
  /-- The state value of the variables. -/
  stVal : Expr

/-- The context of a derivation. -/
structure GCtx where
  /-- The builtin table. -/
  bi : Expr
  /-- The abstract state. -/
  st : StCtx
  /-- The leaf lemmas, by call name. -/
  leaves : Std.HashMap String (Array Name)
  /-- The types of the surface `let`s, by name. -/
  hints : Std.HashMap String Expr

/-- The generator monad. -/
abbrev GenM := ReaderT GCtx TermElabM

/-- A term over the state variables as a function of the state. -/
def abstE (e : Expr) : GenM Expr := do
  let c := (← read).st
  withLocalDeclD `t c.stTy fun t => do
    let ps ← c.proj t
    mkLambdaFVars #[t] (e.replaceFVars c.vars ps)

/-- A closed function of the state read at the current state. -/
def atState (f : Expr) : GenM Expr := return f.beta #[(← read).st.stVal]

/-- The result of a derivation. `exit` is the exit condition, value and bindings. -/
structure GRes where
  /-- The derivation. -/
  proof : Expr
  /-- The value. -/
  val : SVal
  /-- The bindings after a normal run. -/
  N : SEnv
  /-- The exit condition, value and bindings. -/
  exit : Option (Expr × SVal × SEnv) := none

def lamV (v : SVal) : GenM Expr := abstE v.val
def lamL (env : SEnv) : GenM Expr := abstE (mkBList env)

/-- The judgment of a result, as an expected type. -/
def resType (Γ : SEnv) (G e : Expr) (r : GRes) : GenM Expr := do
  let bi := (← read).bi
  let S := (← read).st.stTy
  match r.exit with
  | none =>
    return mkAppN (mkConst ``Hax.Ascent.CorresB) #[S, bi, ← lamL Γ, G, e, ← lamV r.val, ← lamL r.N]
  | some (C, W, T) =>
    return mkAppN (mkConst ``Hax.Ascent.CorresG)
      #[S, bi, ← lamL Γ, G, e, ← abstE C, ← lamV W, ← lamV r.val, ← lamL T, ← lamL r.N]

/-- The result with its judgment as the type of its derivation. -/
def hinted (Γ : SEnv) (G e : Expr) (r : GRes) : GenM GRes := do
  return { r with proof := ← mkExpectedTypeHint r.proof (← resType Γ G e r) }

/-- Instantiate the metavariables of a symbolic value. -/
def instSVal (v : SVal) : MetaM SVal := do
  return { val := ← instantiateMVars v.val, ty? := ← v.ty?.mapM instantiateMVars,
           tm? := ← v.tm?.mapM instantiateMVars }

/-! ### Leaves -/

/-- Read a leaf result value. -/
def readLeafVal (v : Expr) : MetaM SVal := do
  let v ← instantiateMVars v
  match v.getAppFnArgs with
  | (``Hax.Ascent.HaxEnc.enc, #[ty, _, tm]) => typedV ty tm
  | (``Hax.Value.int, #[t]) => typedV intTy t
  | (``Hax.Value.bool, #[t]) => typedV boolTy t
  | (``Hax.Value.unit, _) => unitV
  | _ => return { val := v }

/-- Match the call `f vs` against the leaf lemmas of `f`. With `strict`, a leaf whose
    result type differs from the type hint is skipped. -/
def matchLeaf (f : String) (vs : Array SVal) (hint? : Option Expr) (strict : Bool) :
    GenM (Option (Expr × SVal)) := do
  let ctx ← read
  let vsList ← mkListLit (mkConst ``Hax.Value) (vs.toList.map (·.val))
  for lem in ctx.leaves.getD f #[] do
    let s ← (Meta.saveState : MetaM Meta.SavedState)
    try
      let c ← mkConstWithFreshMVarLevels lem
      let (mvs, bis, concl) ← forallMetaTelescope (← inferType c)
      let some (_, lhs, rhs) := concl.eq? | throwError "no"
      unless ← isDefEq lhs.appFn!.appFn! ctx.bi do throwError "table"
      unless ← isDefEq lhs.appArg! vsList do throwError "args"
      let (``Option.some, #[_, v]) := (← instantiateMVars rhs).getAppFnArgs | throwError "rhs"
      let sv0 ← instSVal { val := v }
      let sv ← if (← instantiateMVars v).hasExprMVar then pure sv0 else readLeafVal v
      -- type hints decide an open element type
      let mut sv := sv
      if (← instantiateMVars v).hasExprMVar then
        let some h := hint? | throwError "open"
        let (``Hax.Ascent.HaxEnc.enc, #[ty, _, _]) := (← instantiateMVars v).getAppFnArgs
          | throwError "open"
        unless ← isDefEq ty h do throwError "hint"
        sv ← readLeafVal v
      else if strict then
        if let (some h, some ty) := (hint?, sv.ty?) then
          unless ← isDefEq ty h do throwError "hint"
      for m in mvs, b in bis do
        let m' ← instantiateMVars m
        if m'.isMVar then
          if b.isInstImplicit then
            let inst ← synthInstance (← inferType m')
            unless ← isDefEq m' inst do throwError "inst"
          else
            let mty ← instantiateMVars (← inferType m')
            if ← isProp mty then
              m'.mvarId!.assign (← proveDecide mty)
      let pf ← instantiateMVars (mkAppN c mvs)
      if pf.hasExprMVar then throwError "open"
      return some (pf, ← instSVal sv)
    catch _ => (s.restore : MetaM Unit)
  return none

/-- Match a call to a tagged runtime name `op#w` on integer arguments with the width
    family lemmas `RuntimeOps.tagged1` and `RuntimeOps.tagged2`. -/
def matchTagged (f : String) (vs : Array SVal) : GenM (Option (Expr × SVal)) := do
  let [op, wS] := f.splitOn "#" | return none
  let some w := wS.toNat? | return none
  let some tms := vs.toList.mapM (·.tm?) | return none
  for (lem, n) in [(``Hax.Ascent.RuntimeOps.tagged1, 1), (``Hax.Ascent.RuntimeOps.tagged2, 2)] do
    unless tms.length == n do continue
    let s ← (Meta.saveState : MetaM Meta.SavedState)
    try
      for v in vs do
        unless ← isDefEq (v.ty?.getD boolTy) intTy do throwError "no"
      let r ← rapp lem
      r.set `f (mkStrLit f); r.set `op (mkStrLit op); r.set `w (mkNatLit w)
      r.set `x tms[0]!
      if n == 2 then r.set `y tms[1]!
      let some (_, lhs0, _) := (← inferType (mkAppN r.c r.mvs)).eq? | throwError "no"
      unless ← isDefEq lhs0.appFn!.appFn! (← read).bi do throwError "table"
      r.side `h₁; r.side `h₂; r.side `h₃
      let pf ← r.done
      let some (_, _, rhs) := (← inferType pf).eq? | throwError "no"
      let (``Option.some, #[_, v]) := rhs.getAppFnArgs | throwError "no"
      return some (pf, ← readLeafVal (← instantiateMVars v).headBeta)
    catch _ => (s.restore : MetaM Unit)
  return none

/-- Match `array_lit` on typed arguments of one type with `RuntimeOps.array_lit_enc`. -/
def matchArrayLit (f : String) (vs : Array SVal) (hint? : Option Expr) :
    GenM (Option (Expr × SVal)) := do
  unless f == "array_lit" do return none
  let some tms := vs.toList.mapM (·.tm?) | return none
  let some tys := vs.toList.mapM (·.ty?) | return none
  let elemTy? ← match tys, hint? with
    | t :: _, _ => pure (some t)
    | [], some h => do
      let h ← whnfR h
      pure (if h.isAppOfArity ``Array 1 then some h.appArg! else none)
    | [], none => pure none
  let some τ := elemTy? | return none
  for t in tys do
    unless ← isDefEq t τ do return none
  let s ← (Meta.saveState : MetaM Meta.SavedState)
  try
    let l ← mkListLit τ tms
    let r ← rapp ``Hax.Ascent.RuntimeOps.array_lit_enc
    r.set `l l
    let some (_, lhs0, _) := (← inferType (mkAppN r.c r.mvs)).eq? | throwError "no"
    unless ← isDefEq lhs0.appFn!.appFn! (← read).bi do throwError "table"
    let pf ← r.done
    let arrTy ← mkAppM ``Array #[τ]
    return some (pf, ← typedV arrTy (← mkAppM ``List.toArray #[l]))
  catch _ =>
    (s.restore : MetaM Unit)
    return none

/-! ### Syntactic scans -/

/-- The names bound by `letBind` or `assign` in an expression, closures excluded. -/
partial def boundNames (e : Expr) : MetaM (List String) := do
  let e ← instantiateMVars e
  let (fn, args) := e.getAppFnArgs
  let sub ← args.toList.mapM fun a => do
    let ty ← inferType a
    if ty.isConstOf ``Hax.ImpExpr then boundNames a
    else if ty.isAppOf ``List then
      match ← listElems? a with
      | some es => do
        let r ← es.mapM fun x => do
          if (← inferType x).isConstOf ``Hax.ImpExpr then boundNames x else pure []
        pure r.flatten
      | none => pure []
    else pure []
  let own := match fn, args with
    | ``Hax.ImpExpr.letBind, #[x, _, _] | ``Hax.ImpExpr.assign, #[x, _] =>
      (strOf? x).toList
    | _, _ => []
  if fn == ``Hax.ImpExpr.lam then return []
  if !fn.isAnonymous && !(fn.getPrefix == ``Hax.ImpExpr) then
    if let some e' ← unfoldDefinition? e then return ← boundNames e'
  return own ++ sub.flatten

/-! ### The derivation -/

def andE (a b : Expr) : Expr := mkApp2 (mkConst ``_root_.And) a b

def trueE : Expr := mkConst ``Bool.true
def falseE : Expr := mkConst ``Bool.false

/-- Merge two values under a condition. -/
def mergeVal (b : Expr) (vt ve : SVal) : MetaM SVal := do
  if ← isDefEqBounded vt.val ve.val then return vt
  if let (some tt, some te, some tyt, some tye) := (vt.ty?, ve.ty?, vt.tm?, ve.tm?) then
    if ← isDefEqBounded tt te then
      return ← typedV tt (← mkIteB b tyt tye)
  return { val := ← mkIteB b vt.val ve.val }

/-- Merge two binding lists under a condition, on their common names. -/
def mergeEnv (b : Expr) (nt ne : SEnv) : MetaM SEnv := do
  let dt := dedupEnv nt []
  let de := dedupEnv ne []
  dt.filterMapM fun (k, vt) => do
    match lookupEnv de k with
    | some ve => return some (k, ← mergeVal b vt ve)
    | none => return none

def isTrueE (e : Expr) : MetaM Bool := return (← instantiateMVars e).isConstOf ``Bool.true
def isFalseE (e : Expr) : MetaM Bool := return (← instantiateMVars e).isConstOf ``Bool.false

mutual

/-- The derivation of `e` from the bindings `Γ` under the guard `G`. -/
partial def gen (Γ : SEnv) (G e : Expr) (hint? : Option Expr := none) : GenM GRes := do
  let e ← instantiateMVars e
  let (fn, args) := e.getAppFnArgs
  let r ← match fn, args with
    | ``Hax.ImpExpr.lit, #[l] => genLit Γ G e l
    | ``Hax.ImpExpr.unitVal, #[] => genUnit Γ G e
    | ``Hax.ImpExpr.var, #[x] => genVar Γ G e x
    | ``Hax.ImpExpr.letBind, #[x, v, b] => genSeqLike Γ G e (some x) v b
    | ``Hax.ImpExpr.seq, #[a, b] => genSeqLike Γ G e none a b
    | ``Hax.ImpExpr.ifThenElse, #[c, t, f] => genIte Γ G e c t f
    | ``Hax.ImpExpr.app, #[f, as] => genApp Γ G e f as hint?
    | ``Hax.ImpExpr.tuple, #[es] => genTuple Γ G e es
    | ``Hax.ImpExpr.proj, #[a, i] => genProj Γ G e a i
    | ``Hax.ImpExpr.typeAscription, #[a, ty] => genPass Γ G ``Hax.Ascent.corresB_typeAscription a (some ty) hint?
    | ``Hax.ImpExpr.borrow, #[a] => genPass Γ G ``Hax.Ascent.corresB_borrow a none hint?
    | ``Hax.ImpExpr.deref, #[a] => genPass Γ G ``Hax.Ascent.corresB_deref a none hint?
    | ``Hax.ImpExpr.cfBreak, #[a] => genBreak Γ G e a
    | ``Hax.ImpExpr.forFold, #[var, lo, hi, body] => genForFold Γ G e var lo hi body
    | ``Hax.ImpExpr.forFoldRev, #[var, lo, hi, body] => genForFold Γ G e var lo hi body true
    | ``Hax.ImpExpr.whileFold, #[c, body] => genWhile Γ G e c body
    | _, _ =>
      if fn.getPrefix == ``Hax.ImpExpr then
        throwError "construct: {fn.getString!}"
      match ← unfoldDefinition? e with
      | some e' =>
        let r ← gen Γ G e' hint?
        return ← hinted Γ G e r
      | none => throwError "construct: not a literal{shortExpr e}"
  hinted Γ G e r

partial def genLit (Γ : SEnv) (G _e l : Expr) : GenM GRes := do
  let l ← instantiateMVars l
  let sv ← match l.getAppFnArgs with
    | (``Hax.ImpLit.int, #[n]) => typedV intTy n
    | (``Hax.ImpLit.bool, #[b]) => typedV boolTy b
    | (``Hax.ImpLit.unit, #[]) => unitV
    | _ => throwError "construct: literal{shortExpr l}"
  let r ← rapp ``Hax.Ascent.corresB_lit
  r.set `bi (← read).bi; r.set `Γ (← lamL Γ); r.set `G G; r.set `l l
  let h ← r.done
  let c ← rapp ``Hax.Ascent.corresB_castV
  c.set `h h; c.set `V (← lamV sv); c.side `hV
  return { proof := ← c.done, val := sv, N := Γ }

partial def genUnit (Γ : SEnv) (G _e : Expr) : GenM GRes := do
  let sv ← unitV
  let r ← rapp ``Hax.Ascent.corresB_unitVal
  r.set `bi (← read).bi; r.set `Γ (← lamL Γ); r.set `G G
  let c ← rapp ``Hax.Ascent.corresB_castV
  c.set `h (← r.done); c.set `V (← lamV sv); c.side `hV
  return { proof := ← c.done, val := sv, N := Γ }

partial def genVar (Γ : SEnv) (G _e x : Expr) : GenM GRes := do
  let some xs := strOf? (← instantiateMVars x) | throwError "construct: variable name"
  let some sv := lookupEnv Γ xs | throwError "unbound: {xs}"
  let r ← rapp ``Hax.Ascent.corresB_var
  r.set `bi (← read).bi; r.set `Γ (← lamL Γ); r.set `G G; r.set `x x; r.set `V (← lamV sv)
  r.side `h
  return { proof := ← r.done, val := sv, N := Γ }

partial def genPass (Γ : SEnv) (G : Expr) (rule : Name) (a : Expr) (ty? : Option Expr)
    (hint? : Option Expr) : GenM GRes := do
  let ra ← gen Γ G a hint?
  if ra.exit.isSome then throwError "construct: exit under a wrapper"
  let r ← rapp rule
  if let some ty := ty? then r.set `ty ty
  r.set `h ra.proof
  return { ra with proof := ← r.done }

/-- `let` and `seq`: the first part, then the rest. -/
partial def genSeqLike (Γ : SEnv) (G _e : Expr) (x? : Option Expr) (v b : Expr) : GenM GRes := do
  let xs? := x?.bind fun x => strOf? x
  let hints := (← read).hints
  let hint? := xs?.bind fun x => hints[x]?
  let r1 ← gen Γ G v hint?
  let bodyEnv (N : SEnv) : SEnv := match xs? with
    | some x => (x, r1.val) :: N
    | none => N
  match r1.exit with
  | none =>
    let rb ← gen (bodyEnv r1.N) G b
    let r ← rapp (if x?.isSome then ``Hax.Ascent.corresB_letBind else ``Hax.Ascent.corresB_seq)
    if let some x := x? then
      r.set `x x; r.set `val v; r.set `body b
      r.set `hval r1.proof; r.set `hbody rb.proof
    else
      r.set `e1 v; r.set `e2 b; r.set `h1 r1.proof; r.set `h2 rb.proof
    r.side `hplain
    return { rb with proof := ← r.done }
  | some (C₁, W₁, T₁) =>
    let Gb ← abstE (andE (← atState G) (← mkEq C₁ falseE))
    let rb ← gen (bodyEnv r1.N) Gb b
    match rb.exit with
    | none =>
      let r ← rapp (if x?.isSome then ``Hax.Ascent.corresG_letBindL else ``Hax.Ascent.corresG_seqL)
      if let some x := x? then r.set `x x; r.set `val v; r.set `body b
      else r.set `e1 v; r.set `e2 b
      r.set `h1 r1.proof; r.set `h2 rb.proof; r.side `hp
      return { proof := ← r.done, val := rb.val, N := rb.N, exit := some (C₁, W₁, T₁) }
    | some (C₂, W₂, T₂) =>
      let r ← rapp (if x?.isSome then ``Hax.Ascent.corresG_letBind else ``Hax.Ascent.corresG_seq)
      if let some x := x? then r.set `x x; r.set `val v; r.set `body b
      else r.set `e1 v; r.set `e2 b
      r.set `h1 r1.proof; r.set `h2 rb.proof; r.side `hp
      let h ← r.done
      let C ← mkAppM ``Bool.or #[C₁, C₂]
      normalizeExit Γ G C C₁ W₁ W₂ T₁ T₂ rb.val rb.N h

/-- Normalize the exit value and bindings of a composite whose exit is `C₁ || C₂` with
    values chosen by `C₁`. -/
partial def normalizeExit (_Γ : SEnv) (_G C C₁ : Expr) (W₁ W₂ : SVal) (T₁ T₂ : SEnv)
    (V : SVal) (N : SEnv) (h : Expr) : GenM GRes := do
  let W ← mergeVal C₁ W₁ W₂
  let T ← mergeEnv C₁ T₁ T₂
  let c ← rapp ``Hax.Ascent.corresG_castVW
  c.set `h h; c.set `W' (← lamV W); c.set `V' (← lamV V); c.side `hW; c.side `hV
  let t ← rapp ``Hax.Ascent.corresG_subT
  t.set `h (← c.done); t.set `T' (← lamL T); t.side `hT
  return { proof := ← t.done, val := V, N, exit := some (C, W, T) }

partial def genIte (Γ : SEnv) (G _e c t f : Expr) : GenM GRes := do
  let rc ← gen Γ G c
  if rc.exit.isSome then throwError "construct: exit in a condition"
  let some B := rc.val.tm? | throwError "type: condition"
  unless ← isDefEq (rc.val.ty?.getD intTy) boolTy do throwError "type: condition"
  let Gt ← abstE (andE (← atState G) (← mkEq B trueE))
  let Gf ← abstE (andE (← atState G) (← mkEq B falseE))
  let rt ← gen rc.N Gt t
  let rf ← gen rc.N Gf f
  if rt.exit.isNone && rf.exit.isNone then
    let r ← rapp ``Hax.Ascent.corresB_ifThenElse
    r.set `c c; r.set `t t; r.set `e f; r.set `C (← abstE B)
    r.set `hc rc.proof; r.set `ht rt.proof; r.set `he rf.proof
    let h ← r.done
    let V ← mergeVal B rt.val rf.val
    let N ← mergeEnv B rt.N rf.N
    let k ← rapp ``Hax.Ascent.corresB_conseqVN
    k.set `h h; k.set `V' (← lamV V); k.set `N' (← lamL N); k.side `hV; k.side `hN
    return { proof := ← k.done, val := V, N }
  let lift (x : GRes) : GenM (Expr × Expr × SVal × SEnv) := do
    match x.exit with
    | some (C, W, T) => return (x.proof, C, W, T)
    | none =>
      let u ← unitV
      let r ← rapp ``Hax.Ascent.CorresG.ofPlain
      r.set `h x.proof; r.set `W (← lamV u); r.set `T (← lamL x.N)
      return (← r.done, falseE, u, x.N)
  let (pt, Ct, Wt, Tt) ← lift rt
  let (pf, Cf, Wf, Tf) ← lift rf
  let r ← rapp ``Hax.Ascent.corresG_ifThenElse
  r.set `c c; r.set `t t; r.set `e f; r.set `B (← abstE B)
  r.set `Ct (← abstE Ct); r.set `Ce (← abstE Cf)
  r.set `hc rc.proof; r.set `ht pt; r.set `he pf
  let h ← r.done
  let C ← mkIteB B Ct Cf
  -- values: a branch that always exits leaves the other; a branch that never exits
  -- leaves the other's exit
  let V ← if ← isTrueE Ct then pure rf.val else if ← isTrueE Cf then pure rt.val
    else mergeVal B rt.val rf.val
  let N ← if ← isTrueE Ct then pure (dedupEnv rf.N []) else if ← isTrueE Cf then
    pure (dedupEnv rt.N []) else mergeEnv B rt.N rf.N
  let W ← if ← isFalseE Ct then pure Wf else if ← isFalseE Cf then pure Wt
    else mergeVal B Wt Wf
  let T ← if ← isFalseE Ct then pure (dedupEnv Tf []) else if ← isFalseE Cf then
    pure (dedupEnv Tt []) else mergeEnv B Tt Tf
  let c ← rapp ``Hax.Ascent.corresG_castVW
  c.set `h h; c.set `W' (← lamV W); c.set `V' (← lamV V); c.side `hW; c.side `hV
  let n ← rapp ``Hax.Ascent.corresG_subN
  n.set `h (← c.done); n.set `N' (← lamL N); n.side `hN
  let tt ← rapp ``Hax.Ascent.corresG_subT
  tt.set `h (← n.done); tt.set `T' (← lamL T); tt.side `hT
  let h ← tt.done
  -- simplify the exit condition
  let (C', lem?) ← simpCond B Ct Cf
  match lem? with
  | none => return { proof := h, val := V, N, exit := some (C, W, T) }
  | some pfFn =>
    let k ← rapp ``Hax.Ascent.corresG_congrC
    k.set `h h; k.set `C' (← abstE C')
    let hcTy ← k.goal `hC
    let pf ← forallTelescope hcTy fun xs _ => do
      let ps ← (← read).st.proj xs[0]!
      let st := (← read).st
      mkLambdaFVars xs ((← pfFn).replaceFVars st.vars ps)
    k.set `hC pf
    return { proof := ← k.done, val := V, N, exit := some (C', W, T) }

/-- A simpler form of `if B then Ct else Cf` with the proof of the equation. -/
partial def simpCond (B Ct Cf : Expr) : GenM (Expr × Option (GenM Expr)) := do
  let t ← isTrueE Ct; let tf ← isFalseE Ct; let f ← isTrueE Cf; let ff ← isFalseE Cf
  if t && ff then return (B, some (mkAppM ``Hax.Ascent.ite_true_false #[B]))
  if tf && f then return (← mkAppM ``not #[B], some (mkAppM ``Hax.Ascent.ite_false_true #[B]))
  if t then return (← mkAppM ``or #[B, Cf], some (mkAppM ``Hax.Ascent.ite_true_left #[B, Cf]))
  if ff then return (← mkAppM ``and #[B, Ct], some (mkAppM ``Hax.Ascent.ite_false_right #[B, Ct]))
  if tf then return (← mkAppM ``and #[← mkAppM ``not #[B], Cf],
    some (mkAppM ``Hax.Ascent.ite_false_left #[B, Cf]))
  if f then return (← mkAppM ``or #[← mkAppM ``not #[B], Ct],
    some (mkAppM ``Hax.Ascent.ite_true_right #[B, Ct]))
  return (← mkIteB B Ct Cf, none)

partial def genArgs (Γ : SEnv) (G : Expr) : List Expr → GenM (Expr × Array SVal × SEnv)
  | [] => do
    let r ← rapp ``Hax.Ascent.corresArgsB_nil
    r.set `bi (← read).bi; r.set `Γ (← lamL Γ); r.set `G G
    return (← r.done, #[], Γ)
  | a :: as => do
    let ra ← gen Γ G a
    if ra.exit.isSome then throwError "construct: exit in an argument"
    let (pr, vs, Nend) ← genArgs ra.N G as
    let r ← rapp ``Hax.Ascent.corresArgsB_cons
    r.set `he ra.proof; r.set `hes pr; r.side `hplain
    return (← r.done, #[ra.val] ++ vs, Nend)

partial def genApp (Γ : SEnv) (G _e f as : Expr) (hint? : Option Expr) : GenM GRes := do
  let some fs := strOf? (← instantiateMVars f) | throwError "construct: call name"
  let some argEs ← listElems? as | throwError "construct: argument list"
  let (pa, vs, Nend) ← genArgs Γ G argEs
  let some (pf, sv) ← (do
      match ← matchLeaf fs vs hint? true with
      | some x => pure (some x)
      | none =>
        match ← matchLeaf fs vs hint? false with
        | some x => pure (some x)
        | none =>
          match ← matchTagged fs vs with
          | some x => pure (some x)
          | none => matchArrayLit fs vs hint?)
    | throwError "leaf: {fs}"
  let r ← rapp ``Hax.Ascent.corresB_app
  r.set `hargs pa; r.set `f f; r.set `V (← lamV sv)
  let hbiTy ← r.goal `hbi
  let st := (← read).st
  let pfl ← forallTelescope hbiTy fun xs _ => do
    let ps ← st.proj xs[0]!
    mkLambdaFVars xs (pf.replaceFVars st.vars ps)
  r.set `hbi pfl
  return { proof := ← r.done, val := sv, N := Nend }

partial def genTuple (Γ : SEnv) (G _e es : Expr) : GenM GRes := do
  let some elems ← listElems? es | throwError "construct: tuple list"
  let (pa, vs, Nend) ← genArgs Γ G elems
  let r ← rapp ``Hax.Ascent.corresB_tuple
  r.set `h pa
  let h ← r.done
  let tys := vs.toList.filterMap (·.ty?)
  let tms := vs.toList.filterMap (·.tm?)
  if vs.size ≥ 2 && tys.length == vs.size && !(← isProdTy tys.getLast!) then
    let sv ← typedV (← mkProdTy tys) (← mkTuple tms)
    let c ← rapp ``Hax.Ascent.corresB_castV
    c.set `h h; c.set `V (← lamV sv); c.side `hV
    return { proof := ← c.done, val := sv, N := Nend }
  let v ← mkAppM ``Hax.Value.tuple #[← mkListLit (mkConst ``Hax.Value) (vs.toList.map (·.val))]
  return { proof := h, val := { val := v }, N := Nend }

partial def genProj (Γ : SEnv) (G _e a i : Expr) : GenM GRes := do
  let ra ← gen Γ G a
  if ra.exit.isSome then throwError "construct: exit in a projection"
  let some n ← (evalNat (← instantiateMVars i)).run | throwError "construct: projection index"
  let sv ← match ra.val.ty?, ra.val.tm? with
    | some ty, some tm => do
      let (cty, ctm) ← projPath ty tm n
      typedV cty ctm
    | _, _ => do
      let v ← mkAppM ``Option.getD #[← mkAppM ``Hax.Value.projIdx #[ra.val.val, i],
        mkConst ``Hax.Value.unit]
      pure { val := v }
  let r ← rapp ``Hax.Ascent.corresB_proj
  r.set `h ra.proof; r.set `i i; r.set `V (← lamV sv)
  r.side `hplain; r.side `hp
  return { proof := ← r.done, val := sv, N := ra.N }

partial def projPath (ty tm : Expr) (i : Nat) : MetaM (Expr × Expr) := do
  let ty' ← whnfR ty
  match ty'.getAppFnArgs with
  | (``Prod, #[α, β]) =>
    if i = 0 then return (α, ← mkAppM ``Prod.fst #[tm])
    else projPath β (← mkAppM ``Prod.snd #[tm]) (i - 1)
  | _ => if i = 0 then return (ty, tm) else throwError "type: projection {i} out of range"

partial def genBreak (Γ : SEnv) (G _e a : Expr) : GenM GRes := do
  let ra ← gen Γ G a
  if ra.exit.isSome then throwError "construct: exit in a break value"
  let r ← rapp ``Hax.Ascent.corresG_cfBreak
  r.set `h ra.proof; r.side `hp
  return { proof := ← r.done, val := ← unitV, N := ra.N, exit := some (trueE, ra.val, ra.N) }

partial def genForFold (Γ : SEnv) (G _e var lo hi body : Expr) (rev : Bool := false) :
    GenM GRes := do
  let some vs := strOf? (← instantiateMVars var) | throwError "construct: loop variable"
  let rlo ← gen Γ G lo
  let rhi ← gen rlo.N G hi
  let (some loT, some hiT) := (rlo.val.tm?, rhi.val.tm?) | throwError "type: loop bounds"
  if rlo.exit.isSome || rhi.exit.isSome then throwError "construct: exit in loop bounds"
  let D := (dedupEnv rhi.N []).filter (·.1 != vs)
  let bound ← boundNames body
  let M := (D.filter (bound.contains ·.1)).reverse
  let tys ← M.mapM fun (k, v) => match v.ty? with
    | some t => pure t
    | none => throwError "type: loop accumulator {k}"
  let A ← mkProdTy tys
  let a₀ ← mkTuple (M.map fun p => p.2.tm?.get!)
  let st := (← read).st
  withLocalDeclD `i intTy fun i => withLocalDeclD `acc A fun acc => do
    let comps ← tupleComps acc M.length
    let mut Λenv : SEnv := []
    for (k, v) in D do
      match M.findIdx? (·.1 == k) with
      | some j => Λenv := Λenv ++ [(k, ← typedV tys[j]! comps[j]!)]
      | none => Λenv := Λenv ++ [(k, v)]
    let ΛL := mkBList Λenv
    let Λl ← withLocalDeclD `s st.stTy fun s => do
      mkLambdaFVars #[s, acc] (ΛL.replaceFVars st.vars (← st.proj s))
    let bstTy ← mkAppM ``Prod #[st.stTy, ← mkAppM ``Prod #[intTy, A]]
    let bst : StCtx := {
      stTy := bstTy, vars := st.vars ++ #[i, acc]
      proj := fun t => do
        let p1 ← mkAppM ``Prod.fst #[t]
        let p2 ← mkAppM ``Prod.snd #[t]
        return (← st.proj p1) ++ #[← mkAppM ``Prod.fst #[p2], ← mkAppM ``Prod.snd #[p2]]
      stVal := ← mkAppM ``Prod.mk #[st.stVal, ← mkAppM ``Prod.mk #[i, acc]] }
    let Γb := (vs, ← typedV intTy i) :: Λenv
    let Gσ ← atState G
    let Gb ← withReader ({ · with st := bst }) do
      abstE (andE Gσ (andE (← mkAppM ``LE.le #[loT, i]) (← mkAppM ``LT.lt #[i, hiT])))
    let rb ← withReader ({ · with st := bst }) (gen Γb Gb body)
    let lam3 (x : Expr) : MetaM Expr := withLocalDeclD `s st.stTy fun s => do
      mkLambdaFVars #[s, i, acc] (x.replaceFVars st.vars (← st.proj s))
    let accOf (env : SEnv) : MetaM Expr := do
      let tms ← M.mapM fun (k, _) => do
        let some sv := lookupEnv env k | throwError "loop: {k} unbound after the body"
        let some tm := sv.tm? | throwError "type: loop accumulator {k} after the body"
        pure tm
      mkTuple tms
    let gTm ← accOf rb.N
    let bodyAbst (x : Expr) : GenM Expr := withReader ({ · with st := bst }) (abstE x)
    let setCommon (r : RApp) : GenM Unit := do
      r.set `hlo rlo.proof; r.set `hhi rhi.proof
      r.set `var var; r.set `body body
      r.set `a₀ (← abstE a₀); r.set `g (← lam3 gTm); r.set `Λ Λl
      r.set `hbody rb.proof
    match rb.exit with
    | none =>
      let r ← rapp (if rev then ``Hax.Ascent.corresB_forFoldRevP else ``Hax.Ascent.corresB_forFoldP)
      setCommon r
      r.side `hinit; r.side `hfresh; r.side `hV; r.side `hstep
      let pf ← r.done
      let gσ := (← lam3 gTm).beta #[st.stVal]
      let fold ← mkAppM (if rev then ``Hax.foldRangeRev else ``Hax.foldRange) #[loT, hiT, a₀, gσ]
      let N ← Λenv.mapM fun (k, v) => do return (k, ← instSValRepl v acc fold)
      return { proof := pf, val := ← unitV, N }
    | some (Cb, Wb, Tb) =>
      if rev then throwError "construct: forFoldRev with break"
      let some wTm := Wb.tm? | throwError "type: break value"
      let gbTm ← accOf Tb
      let r ← rapp ``Hax.Ascent.corresB_forFoldG
      setCommon r
      r.set `w (← lam3 wTm); r.set `gb (← lam3 gbTm); r.set `Cb (← bodyAbst Cb)
      r.side `hinit; r.side `hfresh; r.side `hW; r.side `hV; r.side `hT; r.side `hN
      let pf ← r.done
      let stepFn ← mkLambdaFVars #[i, acc] (← mkAppM ``Hax.Ascent.stepCF #[Cb, wTm, gbTm, gTm])
      let fold ← mkAppM ``Hax.forFold #[loT, hiT, a₀, stepFn]
      let stE ← mkAppM ``Hax.Ascent.cfState #[fold]
      let N ← Λenv.mapM fun (k, v) => do return (k, ← instSValRepl v acc stE)
      return { proof := pf, val := { val := ← mkAppM ``Hax.Ascent.cfVal #[fold] }, N }

/-- Replace a free variable in a symbolic value. -/
partial def instSValRepl (v : SVal) (x r : Expr) : MetaM SVal := do
  return { val := v.val.replaceFVar x r, ty? := v.ty?.map (·.replaceFVar x r),
           tm? := v.tm?.map (·.replaceFVar x r) }

partial def genWhile (Γ : SEnv) (G _e cond body : Expr) : GenM GRes := do
  let D := dedupEnv Γ []
  let bound := (← boundNames body) ++ (← boundNames cond)
  let M := (D.filter (bound.contains ·.1)).reverse
  let tys ← M.mapM fun (k, v) => match v.ty? with
    | some t => pure t
    | none => throwError "type: loop accumulator {k}"
  let A ← mkProdTy tys
  let a₀ ← mkTuple (M.map fun p => p.2.tm?.get!)
  let st := (← read).st
  withLocalDeclD `acc A fun acc => do
    let comps ← tupleComps acc M.length
    let mut Λenv : SEnv := []
    for (k, v) in D do
      match M.findIdx? (·.1 == k) with
      | some j => Λenv := Λenv ++ [(k, ← typedV tys[j]! comps[j]!)]
      | none => Λenv := Λenv ++ [(k, v)]
    let ΛL := mkBList Λenv
    let Λl ← withLocalDeclD `s st.stTy fun s => do
      mkLambdaFVars #[s, acc] (ΛL.replaceFVars st.vars (← st.proj s))
    let lam2 (x : Expr) : MetaM Expr := withLocalDeclD `s st.stTy fun s => do
      mkLambdaFVars #[s, acc] (x.replaceFVars st.vars (← st.proj s))
    let bstTy ← mkAppM ``Prod #[st.stTy, A]
    let bst : StCtx := {
      stTy := bstTy, vars := st.vars ++ #[acc]
      proj := fun t => do
        return (← st.proj (← mkAppM ``Prod.fst #[t])) ++ #[← mkAppM ``Prod.snd #[t]]
      stVal := ← mkAppM ``Prod.mk #[st.stVal, acc] }
    withReader ({ · with st := bst }) do
      let Gc ← abstE (← (atState G : GenM Expr) |>.run { (← read) with st := st })
      let rc ← gen Λenv Gc cond
      if rc.exit.isSome then throwError "construct: exit in a loop condition"
      let some cTm := rc.val.tm? | throwError "type: loop condition"
      let Gb ← abstE (andE (← (atState G : GenM Expr) |>.run { (← read) with st := st })
        (← mkEq cTm trueE))
      let rb0 ← gen rc.N Gb body
      let accOf (env : SEnv) : MetaM Expr := do
        let tms ← M.mapM fun (k, _) => do
          let some sv := lookupEnv env k | throwError "loop: {k} unbound after the body"
          let some tm := sv.tm? | throwError "type: loop accumulator {k} after the body"
          pure tm
        mkTuple tms
      let gTm ← accOf rb0.N
      let (pb, Cb, wTm, gbTm) ← match rb0.exit with
        | some (Cb, Wb, Tb) => do
          let some wTm := Wb.tm? | throwError "type: break value"
          pure (rb0.proof, Cb, wTm, ← accOf Tb)
        | none => do
          let u ← unitV
          let r ← rapp ``Hax.Ascent.CorresG.ofPlain
          r.set `h rb0.proof; r.set `W (← abstE u.val); r.set `T (← abstE (mkBList rb0.N))
          pure (← r.done, falseE, mkConst ``Unit.unit, gTm)
      let r ← rapp ``Hax.Ascent.corresB_whileFoldG
      r.set `cond cond; r.set `body body
      r.set `Λ Λl
      r.set `c (← lam2 cTm); r.set `g (← lam2 gTm); r.set `gb (← lam2 gbTm)
      r.set `w (← lam2 wTm); r.set `Cb (← abstE Cb)
      -- the outer state
      let outer : GCtx := { (← read) with st := st }
      let a₀l ← (abstE a₀ : GenM Expr).run outer
      r.set `a₀ a₀l
      r.set `Γ (← (lamL Γ : GenM Expr).run outer)
      r.set `G G
      r.set `hcond rc.proof; r.set `hbody pb
      r.side `hcondN; r.side `hW; r.side `hV; r.side `hT; r.side `hN
      r.side `hinit
      let htTy ← r.goal `hterm
      r.set `hterm (← (proveTerm htTy : GenM Expr).run outer)
      let pf ← r.done
      let cσ ← mkLambdaFVars #[acc] cTm
      let stepFn ← mkLambdaFVars #[acc] (← mkAppM ``Hax.Ascent.stepCF #[Cb, wTm, gbTm, gTm])
      let fold ← mkAppM ``Hax.whileFold #[a₀, cσ, stepFn]
      let stE ← mkAppM ``Hax.Ascent.cfState #[fold]
      let N ← Λenv.mapM fun (k, v) => do return (k, ← instSValRepl v acc stE)
      return { proof := pf, val := { val := ← mkAppM ``Hax.Ascent.cfVal #[fold] }, N }

/-- Prove the termination side condition of a while loop from a measure read off the
    comparisons of its condition and exit condition. -/
partial def proveTerm (ty : Expr) : GenM Expr := do
  forallTelescope ty fun xs body => do
    let body ← instantiateMVars body
    let (``Hax.WhileFoldStops, #[α, _, init, c, f]) := body.getAppFnArgs
      | throwError "loop: termination goal{shortExpr body}"
    let cands ← measureCands α c f
    let mut lastErr := ""
    for μ in cands do
      let s ← (Term.saveState : TermElabM Term.SavedState)
      try
        let hdecTy ← withLocalDeclD `a α fun a => withLocalDeclD `a' α fun a' => do
          let hc ← mkEq (mkApp c a) trueE
          let cfTy ← whnf (← inferType (mkApp f a))
          let β := cfTy.getArg! 0
          let hf ← mkEq (mkApp f a) (← mkAppOptM ``ControlFlow.Continue #[β, α, a'])
          let concl ← mkAppM ``LT.lt #[mkApp μ a', mkApp μ a]
          mkForallFVars #[a, a'] (← mkArrow hc (← mkArrow hf concl))
        let mv ← mkFreshExprMVar hdecTy
        let tac ← `(tactic| (intro x y hc hf; simp only [Hax.Ascent.stepCF] at hf; split at hf <;> (try cases hf) <;> simp_all [Hax.add, Hax.sub, Hax.lt, Hax.le, Hax.gt, Hax.ge, Hax.bne, Hax.beq] <;> omega))
        Term.withoutErrToSorry <| Term.runTactic mv.mvarId! tac .term
        if (← Core.getMessageLog).hasErrors then throwError "tactic"
        let pf ← mkAppM ``Hax.Ascent.whileFoldStops_of_measure #[μ, ← instantiateMVars mv, init]
        let pf ← mkLambdaFVars xs (← mkExpectedTypeHint pf body)
        return pf
      catch ex =>
        lastErr ← msgStr ex
        (s.restore : TermElabM Unit)
    throwError "loop: while termination not proved ({cands.length} measures; {lastErr})"

/-- Candidate measures `fun a => (y - x).toNat` for the comparisons `x < y`, `x ≤ y` of
    the loop's condition and step. -/
partial def measureCands (α c f : Expr) : MetaM (List Expr) := do
  withLocalDeclD `a α fun a => do
    let body ← instantiateMVars (mkApp2 (mkConst ``_root_.And) (← mkEq (c.beta #[a]) trueE)
      (← mkEq (f.beta #[a]) (f.beta #[a])))
    let mut out := []
    for sub in collectCmp body do
      let (x, y) := sub
      for (p, q) in [(x, y), (y, x)] do
        if (p.containsFVar a.fvarId!) || (q.containsFVar a.fvarId!) then
          for d in [(← mkAppM ``HSub.hSub #[q, p]), (← mkAppM ``HAdd.hAdd #[← mkAppM ``HSub.hSub #[q, p], mkIntLit 1])] do
            out := out ++ [← mkLambdaFVars #[a] (← mkAppM ``Int.toNat #[d])]
    return out
where
  mkIntLit (n : Nat) : Expr := toExpr (n : Int)
  collectCmp (e : Expr) : List (Expr × Expr) :=
    let here := match e.getAppFnArgs with
      | (``Hax.lt, #[ty, _, _, x, y]) | (``Hax.le, #[ty, _, _, x, y])
      | (``Hax.gt, #[ty, _, _, x, y]) | (``Hax.ge, #[ty, _, _, x, y]) =>
        if ty.isConstOf ``Int then [(x, y)] else []
      | _ => []
    here ++ (e.getAppArgs.toList.flatMap collectCmp)

end

/-! ### Leaf lemma index -/

/-- The call name of a leaf lemma `∀ …, bi "f" vs = some v`. -/
def leafNameOf (lem : Name) : MetaM (Option String) := do
  let ty ← inferType (← mkConstWithFreshMVarLevels lem)
  forallTelescope ty fun _ body => do
    let some (_, lhs, _) := body.eq? | return none
    unless lhs.getAppNumArgs ≥ 2 do return none
    return strOf? lhs.appFn!.appArg!

/-- The constants of the module declaring `c` with the prefix `pfx`, in source order: by
    declaration line, and by position in the module for the constants of one line and for
    constants whose declaration range the environment does not carry. -/
def moduleConsts (c pfx : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? c | return #[]
  let names := env.header.moduleData[idx.toNat]!.constNames.filter fun n =>
    pfx.isPrefixOf n && !n.isInternal
  let mut withPos := #[]
  for n in names, i in [0:names.size] do
    let r ← findDeclarationRanges? n
    withPos := withPos.push (n, (r.map (·.range.pos.line)).getD 0, i)
  let lt := fun (a b : Name × Nat × Nat) =>
    a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)
  return (withPos.qsort lt).map (·.1)

/-- Add leaf lemmas to an index. -/
def indexLeaves (idx : Std.HashMap String (Array Name)) (lems : Array Name) :
    MetaM (Std.HashMap String (Array Name)) := do
  let mut idx := idx
  for l in lems do
    if let some f ← leafNameOf l then
      idx := idx.insert f ((idx.getD f #[]).push l)
  return idx

/-- The runtime leaf lemmas of `CatCrypt/Hax/Ascent/RuntimeOps.lean`, in source order. -/
def runtimeLeaves : MetaM (Std.HashMap String (Array Name)) := do
  indexLeaves {} (← moduleConsts ``Hax.Ascent.RuntimeOps.index_int `Hax.Ascent.RuntimeOps)

/-! ### One function -/

/-- The specification of one function for the generator. -/
structure FnSpec where
  /-- The literal, applied to the instance arguments. -/
  lit : Expr
  /-- The printed surface function, applied to the instance arguments. -/
  surface : Expr
  /-- The parameter names of the literal. -/
  params : List String
  /-- The constants read as variables: name, typed value, and a proof of
      `bi name [] = some value`. -/
  globals : List (String × SVal × Expr)
  /-- The builtin table. -/
  bi : Expr
  /-- The leaf lemmas. -/
  leaves : Std.HashMap String (Array Name)
  /-- The types of the surface `let`s. -/
  hints : Std.HashMap String Expr
  /-- The entry environment as a function of the argument tuple, and its binding lemma:
      from the argument tuple type and the entry binding list `Γ₀`, the entry function and
      a proof of `∀ a, G a → Binds (entry a) (Γ₀ a)`. -/
  entry : Expr → Expr → MetaM (Expr × Expr)

/-- The result of the generator on one function. -/
structure FnResult where
  /-- The argument tuple type. -/
  argTy : Expr
  /-- The generated function; `A → β`, or `A → Except βw β` for a function with early
      return. -/
  fn : Expr
  /-- The correspondence theorem statement. -/
  thmTy : Expr
  /-- The correspondence theorem proof. -/
  thm : Expr
  /-- For a function with early return: the merged function `A → β`. -/
  merged? : Option Expr
  /-- For a function with early return: the exit condition, exit value and value, as
      functions of the argument tuple. -/
  parts? : Option (Expr × Expr × Expr) := none
  /-- The surface function read on the argument tuple. -/
  surfaceFn : Expr
  /-- The oracle: whether the generated function is definitionally the surface. -/
  oracle : Bool

/-- The right-nested argument tuple type `τ₁ × (… × (τₙ × Unit))`. -/
def argTupleTy (tys : List Expr) : MetaM Expr :=
  tys.foldrM (fun t acc => mkAppM ``Prod #[t, acc]) (mkConst ``Unit)

/-- The components of an argument tuple. -/
def argComps (a : Expr) : Nat → MetaM (List Expr)
  | 0 => return []
  | n + 1 => do
    return (← mkAppM ``Prod.fst #[a]) :: (← argComps (← mkAppM ``Prod.snd #[a]) n)

/-- **The generator on one function.** The argument tuple is the right-nested product of
    the parameter types of the surface; the entry bindings are the parameters followed by
    the constants. -/
def ascendFn (spec : FnSpec) : TermElabM FnResult := do
  let sty ← inferType spec.surface
  forallTelescopeReducing sty fun xs retTy => do
    let xs ← xs.filterM fun (x : Expr) => return !(← x.fvarId!.getBinderInfo).isInstImplicit
    unless xs.size == spec.params.length do
      throwError "params: the surface has {xs.size} parameters, the literal {spec.params.length}"
    let tys ← xs.toList.mapM fun x => inferType x
    let A ← argTupleTy tys
    withLocalDeclD `a A fun a => do
      let comps ← argComps a tys.length
      let mut Γ₀ : SEnv := []
      for p in spec.params, t in tys, c in comps do
        Γ₀ := Γ₀ ++ [(p, ← typedV t c)]
      for (g, sv, _) in spec.globals do
        Γ₀ := Γ₀ ++ [(g, sv)]
      let st : StCtx := { stTy := A, vars := #[a], proj := fun t => pure #[t], stVal := a }
      let ctx : GCtx := { bi := spec.bi, st, leaves := spec.leaves, hints := spec.hints }
      let G ← withLocalDeclD `a A fun a' => mkLambdaFVars #[a'] (mkConst ``True)
      let r ← (gen Γ₀ G spec.lit).run ctx
      let Γ₀l ← (lamL Γ₀).run ctx
      let (entry, hentry) ← spec.entry A Γ₀l
      let surfaceApp := mkAppN spec.surface comps.toArray
      let surfaceFn ← mkLambdaFVars #[a] surfaceApp
      match r.exit with
      | none =>
        let some tm := r.val.tm? | throwError "type: result value"
        let some β := r.val.ty? | throwError "type: result value"
        let fn ← mkLambdaFVars #[a] tm
        let k ← rapp ``Hax.Ascent.fnCorres_of_corresB
        k.set `h r.proof; k.set `entry entry; k.set `f fn; k.set `hentry hentry
        k.side `hV
        let thm ← k.done
        let thmTy ← instantiateMVars (← inferType thm)
        let oracle ← (do
          unless ← isDefEq β retTy do return false
          withTransparency .default (isDefEqBounded tm surfaceApp))
        return { argTy := A, fn, thmTy, thm, merged? := none, surfaceFn, oracle }
      | some (C, W, _) =>
        let (some wTm, some vTm, some βw, some β) := (W.tm?, r.val.tm?, W.ty?, r.val.ty?)
          | throwError "type: result value"
        let k ← rapp ``Hax.Ascent.fnCorresX_of_corresG
        k.set `h r.proof; k.set `entry entry; k.set `hentry hentry
        k.set `w (← mkLambdaFVars #[a] wTm); k.set `v (← mkLambdaFVars #[a] vTm)
        k.side `hW; k.side `hV
        let thm ← k.done
        let thmTy ← instantiateMVars (← inferType thm)
        let exc ← mkAppOptM ``Except.error #[βw, β, wTm]
        let ok ← mkAppOptM ``Except.ok #[βw, β, vTm]
        let fn ← mkLambdaFVars #[a] (← mkIteB C exc ok)
        let mut merged? := none
        let mut oracle := false
        if ← isDefEq βw β then
          let m ← mkIteB C wTm vTm
          merged? := some (← mkLambdaFVars #[a] m)
          oracle ← (do
            unless ← isDefEq β retTy do return false
            withTransparency .default (isDefEqBounded m surfaceApp))
        let parts := (← mkLambdaFVars #[a] C, ← mkLambdaFVars #[a] wTm, ← mkLambdaFVars #[a] vTm)
        return { argTy := A, fn, thmTy, thm, merged?, surfaceFn, oracle, parts? := some parts }

end Hax.Ascent.Gen

end

end
