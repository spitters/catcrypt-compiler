/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.Generate
public import CatCrypt.Hax.Ascent.Structs
public import CatCrypt.Hax.Ascent.Deps
public meta import Lean

/-!
# The generator on a whole extraction

`hax_ascend Ns` and `#hax_coverage Ns` read a haxpipeT extraction in the namespace `Ns`
from the environment, assemble its builtin table, and run the generator of
`CatCrypt/Hax/Ascent/Generate.lean` on every `_impExpr` literal.

## The table

The extraction is found through its dependency class `Ns.NsDeps`; its constants are read
in source order from the module that declares the class.

* Structs: an abbreviation `S_T` with a constructor `S : T₀ → … → S_T` is a struct of
  arity `n`; a definition `(x : S_T) → _` whose body is a path of `Prod.fst`/`Prod.snd` from
  `x` is a projection, its name the literal's projection name. A constructor returning
  another type (a pass-through struct) is left out and noted. A struct of arity at least
  two whose last field has a product type is encoded at the product of its field types
  with the last one under `Boxed` (`StructInfo.encTy`), so that its encoding has one
  component per field.
* Dependencies: every field of the class, including fields without arguments, is a
  `DepMethod` over the right-nested tuple of its argument types. A field whose name is a
  runtime operation is left out and noted.
* Struct updates the literals call get entries under their literal names ahead of the
  struct table.

The generated declarations are `Ns.HaxGen.structs`, `Ns.HaxGen.deps`, `Ns.HaxGen.table`
(`updates ++ structsTable structs ++ depsTable deps`), one leaf lemma `Ns.HaxLeaf.«name»`
per struct and dependency name the literals use, and `Ns.HaxGen.fns`, `Ns.HaxGen.names`,
`Ns.HaxGen.notIn_fns`, `Ns.HaxGen.builtins := extBuiltins table fns`.

## Local functions

A literal `Ns.f_impExpr` with a surface function `Ns.f` is a local function. Its parameters
are the leading rebindings `let x := x` of the literal, as many as the surface has
explicit parameters; its globals are the variables it reads that name a constant of the
extraction (a function without parameters, or a dependency field without arguments) and
are neither parameters nor bound in the literal; its calls are the call names that name a
local function. The functions are generated in dependency order; the functions on a cycle
are excluded and reported.

For each function `f` the run declares `Ns.HaxGen.fn_f : ExtFn`, the generated surface
`Ns.HaxGen.f.gen` (and `Ns.HaxGen.f.merged` for a function with early return), the
correspondence `Ns.HaxGen.f.corres` under the table of the functions before it, its form
`Ns.HaxGen.f.corres_full` under the table of all functions, the oracle equation
`Ns.HaxGen.f.oracle` when the generated function is definitionally the surface, and the call
lemma `Ns.HaxCall.f`, which later functions use as the leaf of `f`, specialized to their
prefix (`Ns.HaxGen.g.call_f`).

## Reports

A report line gives the function, `proved`, `proved (early return)`, `failed`, `timeout` or
`excluded`, the time, and the oracle status and phase times, or the first line of the
failure.

Each function runs under heartbeat budgets of its own, counted from its start: one for the
generation and its declarations, one for its call lemma and one for its correspondence
under the whole table. A function that exceeds a budget is reported `timeout`, with the
phase, and its declarations are discarded; the run continues with the next function. The
reading of each literal, of its parameters and bound names, and each leaf lemma likewise
run under budgets of their own; a leaf lemma that fails is noted and left out.

The constructs outside the generator (`lam`, `forFoldRevReturn`, `whileFoldReturn`,
`cfContinue`, `cfBreakContinue`, and the pre-pipeline constructs) are counted per function;
the generator reads `match_` as the `Option` match on a variable and as a single arm whose
pattern is a tuple of variables.
`coverageRun` runs the same on an extraction module from `IO`.

## Main definitions

* `collectStructs`, `collectDeps`, `ascendExtraction`, `coverageRun`
* the commands `hax_ascend` and `#hax_coverage`
-/

@[expose] public section

meta section

open Lean Meta Elab
open Lean.Elab.Term (TermElabM)

namespace Hax.Ascent.Gen

/-! ### Extraction metadata -/

/-- The last component of a name. -/
def lastStr : Name → String
  | .str _ s => s
  | _ => ""

/-- The string without its last `k` characters. -/
def dropEnd (s : String) (k : Nat) : String := String.ofList (s.toList.take (s.length - k))

/-- The constant `c` applied to the instances of `insts` its leading instance binders
    ask for. -/
def applyInsts (c : Name) (insts : Array Expr) : MetaM Expr := do
  let ci ← getConstInfo c
  let mut e := Lean.mkConst c (ci.levelParams.map fun _ => Level.zero)
  let mut ty := ci.type
  repeat
    match ty with
    | .forallE _ d b .instImplicit =>
      let some i ← insts.findM? fun i => do isDefEq (← inferType i) d
        | throwError "instance {d}"
      e := mkApp e i
      ty := b.instantiate1 i
    | _ => break
  return e

/-- The projections from `x` to `e`, innermost first; `true` is `Prod.snd`. -/
partial def projOps (e x : Expr) : Option (List Bool) :=
  if e == x then some [] else
  match e with
  | .proj _ i e' => (projOps e' x).map (· ++ [i == 1])
  | .mdata _ e' => projOps e' x
  | .app (.app (.app (.const n _) _) _) e' =>
    if n == ``Prod.fst then (projOps e' x).map (· ++ [false])
    else if n == ``Prod.snd then (projOps e' x).map (· ++ [true]) else none
  | _ => none

/-- A struct of an extraction. -/
structure StructInfo where
  /-- The constructor name of the literal. -/
  lit : String
  /-- The constructor. -/
  ctor : Name
  /-- The abbreviation `S_T`. -/
  tyName : Name
  /-- The field count. -/
  arity : Nat
  /-- The field types. -/
  fieldTys : Array Expr
  /-- The projections: literal name, declaration, field index. -/
  projs : Array (String × Name × Nat)
  /-- The last field has a product type: the struct is encoded at the product of its
      field types with the last one under `Boxed`. -/
  boxed : Bool := false

/-- The type a struct is encoded at: the abbreviation `S_T`, or, for a struct whose last
    field has a product type, the product of the field types with the last one under
    `Boxed`. -/
def StructInfo.encTy (s : StructInfo) : MetaM Expr := do
  unless s.boxed do return mkConst s.tyName
  let tys := s.fieldTys.toList
  let last ← mkAppM ``Hax.Ascent.Boxed #[tys.getLast!]
  mkProdTy (tys.dropLast ++ [last])

/-- The type of field `i` as a component of `StructInfo.encTy`. -/
def StructInfo.compTy (s : StructInfo) (i : Nat) : MetaM Expr := do
  if s.boxed && i + 1 == s.arity then mkAppM ``Hax.Ascent.Boxed #[s.fieldTys[i]!]
  else return s.fieldTys[i]!

/-- The structs of an extraction, from its `S_T` abbreviations, constructors and
    projections; the second component lists the structs left out, with the reason. -/
def collectStructs (ns : Name) (consts : Array Name) :
    MetaM (Array StructInfo × Array String) := do
  let env ← getEnv
  let mut out := #[]
  let mut skipped := #[]
  for c in consts do
    let s := lastStr c
    unless c.getPrefix == ns && s.endsWith "_T" do continue
    let S := dropEnd s 2
    let ctor := Name.str ns S
    unless env.contains ctor do continue
    let cty ← inferType (mkConst ctor)
    let info? ← forallTelescope cty fun xs r => do
      unless r.isConstOf c do return none
      return some (xs.size, ← xs.mapM inferType)
    let some (arity, tys) := info? | skipped := skipped.push s!"{S}: pass-through struct"; continue
    if arity == 0 then continue
    let boxed ← if arity ≥ 2 then isProdTy tys.back! else pure false
    let mut projs := #[]
    for p in consts do
      unless p.getPrefix == ns do continue
      let some ci := env.find? p | continue
      let .forallE _ (.const d _) body _ := ci.type | continue
      unless d == c && !body.isForall && !body.hasLooseBVars do continue
      let some v := ci.value? | continue
      let .lam _ _ b _ := v | continue
      let some ops := projOps b (.bvar 0) | continue
      let i := (ops.filter id).length
      let ok : Bool := match ops.getLast? with
        | some false => decide (i + 1 < arity)
        | _ => i + 1 == arity
      if ok then projs := projs.push (lastStr p, p, i)
    out := out.push { lit := S, ctor, tyName := c, arity, fieldTys := tys, projs, boxed }
  return (out, skipped)

/-- The methods of a dependency class: name, projection, argument types, result
    type. -/
def collectDeps (cls : Name) : MetaM (Array (String × Name × List Expr × Expr)) := do
  let env ← getEnv
  let fields := getStructureFieldsFlattened env cls false
  fields.filterMapM fun f => do
    let proj := cls ++ f
    let ty ← inferType (mkConst proj)
    forallTelescope ty fun xs r => do
      if xs.size < 1 then return none
      let tys ← xs[1:].toArray.toList.mapM fun x => inferType x
      if r.hasLooseBVars || (← tys.anyM fun t => return t.hasFVar) then return none
      return some (f.toString, proj, tys, r)

/-- The untagged names of the runtime table. -/
def runtimeNames : MetaM (List String) := do
  let some v := (← getConstInfo ``Hax.Ascent.runtimeTable).value? | return []
  let some es ← listElems? v | return []
  es.filterMapM fun e => do
    let e ← whnfR e
    match e.getAppFnArgs with
    | (``Prod.mk, #[_, _, k, _]) => return strOf? k
    | _ => return none

/-- A tagged runtime name `op#w`, with `w` decimal digits or `size`. -/
def isTagged (s : String) : Bool :=
  match s.splitOn "#" with
  | [_, w] => w == "size" || (!w.isEmpty && w.all Char.isDigit)
  | _ => false

/-- The call names, variable names and constructors of a literal. -/
structure Scan where
  /-- The call names. -/
  apps : Array String := #[]
  /-- The variable names. -/
  vars : Array String := #[]
  /-- The constructor counts. -/
  ctors : Std.HashMap String Nat := {}
  deriving Inhabited

/-- Scan a literal. -/
partial def scanLit (e : Expr) (acc : Scan) : Scan :=
  match e with
  | .mdata _ b => scanLit b acc
  | .app .. =>
    let (fn, args) := e.getAppFnArgs
    let acc := if fn.getPrefix == ``Hax.ImpExpr then
        { acc with ctors := acc.ctors.insert (lastStr fn) (acc.ctors.getD (lastStr fn) 0 + 1) }
      else acc
    let acc := match fn, args with
      | ``Hax.ImpExpr.app, #[f, _] => match strOf? f with
        | some s => { acc with apps := acc.apps.push s }
        | none => acc
      | ``Hax.ImpExpr.var, #[x] => match strOf? x with
        | some s => { acc with vars := acc.vars.push s }
        | none => acc
      | _, _ => acc
    args.foldl (fun a x => scanLit x a) acc
  | .const n _ =>
    if n.getPrefix == ``Hax.ImpExpr then
      { acc with ctors := acc.ctors.insert (lastStr n) (acc.ctors.getD (lastStr n) 0 + 1) }
    else acc
  | _ => acc

/-- The parameter names of a literal: its leading rebindings `let x := x`. -/
partial def leadingParams (e : Expr) : List String :=
  match e.getAppFnArgs with
  | (``Hax.ImpExpr.letBind, #[x, v, b]) =>
    match v.getAppFnArgs, strOf? x with
    | (``Hax.ImpExpr.var, #[y]), some xs =>
      if strOf? y == some xs then xs :: leadingParams b else []
    | _, _ => []
  | _ => []

/-- The `let` types of a surface body, first occurrence per name. -/
partial def letTypes (e : Expr) (acc : Std.HashMap String Expr) : Std.HashMap String Expr :=
  match e with
  | .letE n ty v b _ =>
    let acc := if acc.contains n.toString || ty.hasLooseBVars then acc
      else acc.insert n.toString ty
    letTypes b (letTypes v acc)
  | .app f a => letTypes a (letTypes f acc)
  | .lam _ _ b _ => letTypes b acc
  | .mdata _ b => letTypes b acc
  | _ => acc

/-- Dependency order of `names` under `deps`; the names on a cycle are returned
    separately. -/
partial def topoOrder (names : Array String) (deps : String → List String) :
    Array String × Array String := Id.run do
  let mut state : Std.HashMap String Nat := {}
  let mut order := #[]
  let mut cyclic := #[]
  for n in names do
    (state, order, cyclic) := visit n state order cyclic []
  return (order, cyclic)
where
  /-- Visit a name below the names of `stack`. -/
  visit (n : String) (state : Std.HashMap String Nat) (order cyclic : Array String)
      (stack : List String) : Std.HashMap String Nat × Array String × Array String :=
    match state[n]? with
    | some _ => (state, order, cyclic)
    | none =>
      if stack.contains n then
        (state, order, (cyclic ++ (n :: stack.takeWhile (· != n)).toArray))
      else Id.run do
        let mut st := state
        let mut o := order
        let mut cy := cyclic
        for d in deps n do
          if d == n then cy := cy.push n
          else if stack.contains d then
            cy := cy ++ (d :: n :: stack.takeWhile (· != d)).toArray
          else (st, o, cy) := visit d st o cy (n :: stack)
        st := st.insert n 1
        unless cy.contains n do o := o.push n
        return (st, o, cy)

/-! ### Declarations -/

/-- Declare a theorem. -/
def addThm (n : Name) (ty val : Expr) : MetaM Unit := do
  let ty ← instantiateMVars ty
  let val ← instantiateMVars val
  addDecl (.thmDecl { name := n, levelParams := [], type := ty, value := val })

/-- Declare a noncomputable definition. -/
def addDefn (n : Name) (ty val : Expr) : MetaM Unit := do
  let ty ← instantiateMVars ty
  let val ← instantiateMVars val
  let d : DefinitionVal := {
    name := n
    levelParams := []
    type := ty
    value := val
    hints := ReducibilityHints.regular 0
    safety := DefinitionSafety.safe }
  addDecl (Declaration.defnDecl d)
  modifyEnv (addNoncomputable · n)

/-- The report line of one function. -/
structure FnReport where
  /-- The function. -/
  name : String
  /-- `proved`, `proved (early return)`, `failed`, `timeout` (the function exceeded its
      heartbeat budget) or `excluded`. -/
  status : String
  /-- The oracle status and phase times, or the cause of the failure. -/
  detail : String := ""
  /-- The time in milliseconds. -/
  ms : Nat := 0

/-- Run `x` under a heartbeat budget of its own, counted from the start of `x`. A failure,
    including an exceeded heartbeat or recursion limit, restores the state and returns the
    first 300 characters of the error, on one line. -/
def budgeted {α : Type} (x : TermElabM α) : TermElabM (Except String α) := do
  let saved ← saveState
  tryCatchRuntimeEx (return .ok (← withCurrHeartbeats x)) fun ex => do
    saved.restore
    return .error ((← msgStr ex).replace "\n" " ")

/-- The right-nested argument tuple `(x₁, (…, (xₙ, ())))`. -/
def mkArgTuple : List Expr → MetaM Expr
  | [] => return mkConst ``Unit.unit
  | x :: xs => do mkAppM ``Prod.mk #[x, ← mkArgTuple xs]

/-- Run the generator on every function of the extraction `ns`: declare the struct and
    dependency table, the leaf lemmas, and for each function its generated surface, its
    correspondence theorems, its oracle equation and its call lemma. With `only?`, the
    functions outside the list are skipped. -/
def ascendExtraction (ns : Name) (only? : Option (List String) := none) :
    TermElabM (Array FnReport × Array String) := do
  let env ← getEnv
  let clsName := Name.str ns (lastStr ns ++ "Deps")
  let anchor ← if env.contains clsName then pure clsName else
    match (env.constants.map₁.toList.find? fun (n, _) =>
        n.getPrefix == ns && (lastStr n).endsWith "_impExpr") with
    | some (n, _) => pure n
    | none => throwError "hax_ascend: no extraction in {ns}"
  let consts ← moduleConsts anchor ns
  let mut notes : Array String := #[]
  let (structs, skippedS) ← collectStructs ns consts
  notes := notes ++ skippedS
  let rtNames ← runtimeNames
  let hasCls := env.contains clsName && isClass env clsName
  let body (insts : Array Expr) : TermElabM (Array FnReport × Array String) := do
    let mut notes := notes
    let gen (s : String) : Name := ns ++ `HaxGen ++ Name.mkSimple s
    -- the struct types encoded with a `Boxed` last field, by their abbreviation and its body
    let mut boxes0 : Array (Expr × Expr) := #[]
    for s in structs do
      unless s.boxed do continue
      let eTy ← s.encTy
      boxes0 := boxes0.push (mkConst s.tyName, eTy)
      if let some v := (← getConstInfo s.tyName).value? then boxes0 := boxes0.push (v, eTy)
    let boxes := boxes0
    let normTy (t : Expr) : MetaM Expr := do
      let t ← instantiateMVars t
      return t.replace fun e => (boxes.find? (·.1 == e)).map (·.2)
    -- structs
    let pairTy ← mkAppM ``Prod #[mkConst ``String, mkConst ``Nat]
    let specs ← structs.toList.mapM fun s => do
      let projs ← mkListLit pairTy (← s.projs.toList.mapM fun (l, _, i) =>
        mkAppM ``Prod.mk #[mkStrLit l, mkNatLit i])
      mkAppM ``Hax.Ascent.StructSpec.mk #[mkStrLit s.lit, mkNatLit s.arity, projs]
    let structsE ← mkListLit (mkConst ``Hax.Ascent.StructSpec) specs
    addDefn (gen "structs") (mkApp (mkConst ``List [Level.zero]) (mkConst ``Hax.Ascent.StructSpec))
      structsE
    -- dependency methods
    let deps ← if hasCls then collectDeps clsName else pure #[]
    let mut depElems : Array (String × Expr × Name × List Expr × Expr) := #[]
    for (f, proj, tys, r) in deps do
      if rtNames.contains f || isTagged f then
        notes := notes.push s!"dependency {f}: its name is a runtime operation"; continue
      let res ← budgeted do
        let A ← argTupleTy tys
        let fnLam ← withLocalDeclD `p A fun p => do
          let cs ← argComps p tys.length
          mkLambdaFVars #[p] (mkAppN (← applyInsts proj insts) cs.toArray)
        mkAppM ``Hax.Ascent.DepMethod.mk #[mkStrLit f, A, r, fnLam]
      match res with
      | .ok m => depElems := depElems.push (f, m, proj, tys, r)
      | .error _ =>
        notes := notes.push s!"dependency {f}: no injective encoding of its argument types"
    let depsE ← mkListLit (mkConst ``Hax.Ascent.DepMethod) (depElems.toList.map (·.2.1))
    addDefn (gen "deps") (← mkForallFVars insts (← inferType depsE)) (← mkLambdaFVars insts depsE)
    -- literals
    let lits := consts.filter fun c => c.getPrefix == ns && (lastStr c).endsWith "_impExpr"
    let mut infos : Std.HashMap String (Name × Name × Expr × Scan) := {}
    let mut allApps : Std.HashSet String := {}
    for l in lits do
      let f := dropEnd (lastStr l) 8
      let sur := Name.str ns f
      unless (← getEnv).contains sur do continue
      let .ok (some lb) ← budgeted do unfoldDefinition? (← applyInsts l insts)
        | notes := notes.push s!"literal {f}: its value could not be read"; continue
      let sc := scanLit lb {}
      for a in sc.apps do allApps := allApps.insert a
      for a in sc.vars do allApps := allApps.insert a
      infos := infos.insert f (sur, l, lb, sc)
    let fnNames := (lits.filterMap fun l =>
      let f := dropEnd (lastStr l) 8
      if infos.contains f then some f else none)
    -- struct updates the literals call, keyed by literal names ahead of the struct table
    let entryTy ← mkAppM ``Prod #[mkConst ``String, mkConst ``Hax.Ascent.Leaf]
    let mut updEntries := #[]
    for s in structs do
      for i in [0:s.arity] do
        let key := s!"struct_update#{s.lit}#{i}#{s.arity}"
        unless allApps.contains key do continue
        updEntries := updEntries.push (← mkAppOptM ``Prod.mk #[mkConst ``String,
          mkConst ``Hax.Ascent.Leaf, mkStrLit key,
          ← mkAppM ``Hax.Ascent.updateLeaf #[mkNatLit i, mkNatLit s.arity]])
    let updatesE ← mkListLit entryTy updEntries.toList
    let tableE ← mkAppM ``HAppend.hAppend #[updatesE,
      ← mkAppM ``HAppend.hAppend #[← mkAppM ``Hax.Ascent.structsTable #[mkConst (gen "structs")],
      ← mkAppM ``Hax.Ascent.depsTable #[mkAppN (mkConst (gen "deps")) insts]]]
    addDefn (gen "table") (← mkForallFVars insts (mkConst ``Hax.Ascent.Table))
      (← mkLambdaFVars insts tableE)
    let T := mkAppN (mkConst (gen "table")) insts
    -- leaf lemmas of structs and methods
    let leafNs := ns ++ `HaxLeaf
    let valTy := mkConst ``Hax.Value
    let fnsTy := mkApp (mkConst ``List [Level.zero]) (mkConst ``Hax.Ascent.ExtFn)
    let mkLeafThm (name : String) (argTys : List Expr) (l : MetaM Expr)
        (transport : Array Expr → MetaM Expr) (rhs : Array Expr → MetaM Expr) : MetaM Unit := do
      withLocalDeclD `fns fnsTy fun fns => do
        let xs ← argTys.toArray.mapIdxM fun i t => pure (Name.mkSimple s!"x{i}", t)
        withLocalDeclsDND xs fun xs => do
          let vs ← mkListLit valTy (← (xs.toList.zip argTys).mapM fun (x, t) => mkEnc t x)
          let bi ← mkAppM ``Hax.Ascent.extBuiltins #[T, fns]
          let lhs := mkApp2 bi (mkStrLit name) vs
          let ty ← mkEq lhs (← mkAppM ``Option.some #[← rhs xs])
          let r ← rapp ``Hax.Ascent.extBase_leaf
          r.set `T T; r.set `fns fns; r.set `f (mkStrLit name); r.set `vs vs
          r.set `l (← l)
          r.side `hrt; r.side `htag; r.side `hl
          let pf ← mkEqTrans (← r.done) (← transport xs)
          let pf ← mkExpectedTypeHint pf ty
          addThm (Name.str leafNs name) (← mkForallFVars (insts ++ #[fns] ++ xs) ty)
            (← mkLambdaFVars (insts ++ #[fns] ++ xs) pf)
    let mut leafNames : Array Name := #[]
    for (f, m, proj, tys, r) in depElems do
      unless allApps.contains f do continue
      match ← budgeted (mkLeafThm f tys (mkAppM ``Hax.Ascent.DepMethod.leaf #[m])
          (fun xs => do mkAppM ``Hax.Ascent.DepMethod.leaf_apply #[m, ← mkArgTuple xs.toList])
          (fun xs => do mkEnc r (mkAppN (← applyInsts proj insts) xs))) with
      | .ok () => leafNames := leafNames.push (Name.str leafNs f)
      | .error e => notes := notes.push s!"leaf {f}: {e}"
    for s in structs do
      let sty ← s.encTy
      if allApps.contains s.lit then
        match ← budgeted (mkLeafThm s.lit s.fieldTys.toList
            (mkAppM ``Hax.Ascent.ctorLeaf #[mkNatLit s.arity])
            (fun xs => do
              if s.arity == 1 then mkAppM ``Hax.Ascent.ctorLeaf_one #[xs[0]!]
              else
                let r ← rapp ``Hax.Ascent.ctorLeaf_prod
                r.set `p (← mkExpectedTypeHint (mkAppN (mkConst s.ctor) xs) sty)
                r.set `n (mkNatLit s.arity)
                r.side `hlen; r.side `hn
                r.done)
            (fun xs => mkEnc sty (mkAppN (mkConst s.ctor) xs))) with
        | .ok () => leafNames := leafNames.push (Name.str leafNs s.lit)
        | .error e => notes := notes.push s!"leaf {s.lit}: {e}"
      for (pl, pd, i) in s.projs do
        unless allApps.contains pl do continue
        let fty := if s.arity == 1 then sty else s.fieldTys[i]!
        match ← budgeted (mkLeafThm pl [sty]
            (mkAppM ``Hax.Ascent.projLeaf #[mkNatLit i, mkNatLit s.arity])
            (fun xs => do
              if s.arity == 1 then mkAppM ``Hax.Ascent.projLeaf_one #[xs[0]!]
              else
                let r ← rapp ``Hax.Ascent.projLeaf_prod
                r.set `i (mkNatLit i); r.set `p xs[0]!; r.set `n (mkNatLit s.arity)
                r.set `β (← s.compTy i)
                r.side `hn
                r.done)
            (fun xs => mkEnc fty (mkApp (mkConst pd) xs[0]!))) with
        | .ok () => leafNames := leafNames.push (Name.str leafNs pl)
        | .error e => notes := notes.push s!"leaf {pl}: {e}"
      for i in [0:s.arity] do
        let un := s!"struct_update#{s.lit}#{i}#{s.arity}"
        unless allApps.contains un do continue
        let fty := s.fieldTys[i]!
        match ← budgeted (mkLeafThm un [sty, fty]
            (mkAppM ``Hax.Ascent.updateLeaf #[mkNatLit i, mkNatLit s.arity])
            (fun xs => do
              if s.arity == 1 then mkAppM ``Hax.Ascent.updateLeaf_one #[xs[0]!, xs[1]!]
              else
                let r ← rapp ``Hax.Ascent.updateLeaf_prod
                r.set `β (← s.compTy i)
                r.set `i (mkNatLit i); r.set `p xs[0]!; r.set `v xs[1]!; r.set `n (mkNatLit s.arity)
                r.side `hn
                r.done)
            (fun xs => do
              if s.arity == 1 then mkEnc sty xs[1]!
              else mkEnc sty (← mkAppOptM ``Hax.Ascent.fieldSet
                #[mkNatLit i, sty, ← s.compTy i, none, xs[0]!, xs[1]!]))) with
        | .ok () => leafNames := leafNames.push (Name.str leafNs un)
        | .error e => notes := notes.push s!"leaf {un}: {e}"
    -- local functions: parameters, globals, calls, order
    -- a function whose parameters or bound names could not be read, with the error
    let mut preFail : Std.HashMap String String := {}
    let mut params : Std.HashMap String (List String) := {}
    for f in fnNames do
      let (sur, _, lb, _) := infos[f]!
      let res ← budgeted do
        let sty ← inferType (← applyInsts sur insts)
        forallTelescopeReducing sty fun xs _ => do
          let xs ← xs.filterM fun (x : Expr) => return !(← x.fvarId!.getBinderInfo).isInstImplicit
          return xs.size
      match res with
      | .ok n => params := params.insert f ((leadingParams lb).take n)
      | .error e => preFail := preFail.insert f s!"parameters: {e}"
    let consts0 := fnNames.filter fun f => !preFail.contains f && (params.getD f []).isEmpty
    let zeroDeps := (depElems.filter fun d => d.2.2.2.1.isEmpty).map (·.1)
    let mut globalsOf : Std.HashMap String (List String) := {}
    let mut callsOf : Std.HashMap String (List String) := {}
    for f in fnNames do
      let (_, _, lb, sc) := infos[f]!
      let mut bound : List String := []
      match ← budgeted (boundNames lb) with
      | .ok b => bound := b
      | .error e =>
        unless preFail.contains f do preFail := preFail.insert f s!"bound names: {e}"
      let ps := params.getD f []
      let gs := (sc.vars.toList.eraseDups).filter fun v =>
        (consts0.contains v || zeroDeps.contains v) && !ps.contains v && !bound.contains v
      let cs := (sc.apps.toList.eraseDups).filter fun a => infos.contains a
      globalsOf := globalsOf.insert f gs
      callsOf := callsOf.insert f cs
    let (order, cyclic) := topoOrder fnNames fun f =>
      (callsOf.getD f []) ++ ((globalsOf.getD f []).filter infos.contains)
    let mut reports : Array FnReport := #[]
    for f in cyclic.toList.eraseDups do
      reports := reports.push { name := f, status := "excluded", detail := "recursion" }
    -- ExtFn constants
    let strTy := mkConst ``String
    for f in order do
      let (_, l, _, _) := infos[f]!
      let v ← mkAppM ``Hax.Ascent.ExtFn.mk #[mkStrLit f,
        ← mkListLit strTy ((params.getD f []).map mkStrLit),
        ← mkListLit strTy ((globalsOf.getD f []).map mkStrLit), ← applyInsts l insts]
      addDefn (gen s!"fn_{f}") (← mkForallFVars insts (mkConst ``Hax.Ascent.ExtFn))
        (← mkLambdaFVars insts v)
    let fnE (f : String) : Expr := mkAppN (mkConst (gen s!"fn_{f}")) insts
    let extFnTy := mkConst ``Hax.Ascent.ExtFn
    let allFns ← mkListLit extFnTy (order.toList.map fnE)
    addDefn (gen "fns") (← mkForallFVars insts fnsTy) (← mkLambdaFVars insts allFns)
    let namesE ← mkListLit strTy (order.toList.map mkStrLit)
    addDefn (gen "names") (mkApp (mkConst ``List [Level.zero]) strTy) namesE
    let notInEq ← withLocalDeclD `f strTy fun fv => do
      let lhs ← mkAppM ``Hax.Ascent.notIn #[mkAppN (mkConst (gen "fns")) insts]
      let rhs ← mkLambdaFVars #[fv] (← mkAppM ``not #[← mkAppM ``List.contains #[mkConst (gen "names"), fv]])
      mkEq lhs rhs
    let some (_, notInL, _) := notInEq.eq? | throwError "no"
    addThm (gen "notIn_fns") (← mkForallFVars insts notInEq)
      (← mkLambdaFVars insts (← mkExpectedTypeHint (← mkEqRefl notInL) notInEq))
    addDefn (gen "builtins") (← mkForallFVars insts (mkConst ``Hax.Builtins))
      (← mkLambdaFVars insts (← mkAppM ``Hax.Ascent.extBuiltins #[T, mkAppN (mkConst (gen "fns")) insts]))
    -- the generator, in dependency order
    let rtIdx ← withCurrHeartbeats runtimeLeaves
    let mut idx ← withCurrHeartbeats (indexLeaves rtIdx leafNames)
    let tableNames : List String := (structs.toList.flatMap fun s =>
        s.lit :: (s.projs.toList.map (·.1)) ++
          ((List.range s.arity).map fun i => s!"struct_update#{s.lit}#{i}#{s.arity}")) ++
      depElems.toList.map (·.1)
    let mut k := 0
    for f in order do
      let pre := order.toList.take k
      k := k + 1
      if let some sel := only? then
        unless sel.contains f do continue
      let (sur, _, _, sc) := infos[f]!
      let unsupported := ["lam", "forFoldRevReturn",
        "whileFoldReturn", "cfContinue", "cfBreakContinue", "assign", "forLoop", "forLoopRev",
        "whileLoop", "break_", "continue_", "earlyReturn", "questionMark"]
      let census := unsupported.filterMap fun c =>
        (sc.ctors[c]?).map fun n => s!"{c}×{n}"
      if let some e := preFail[f]? then
        reports := reports.push { name := f, status := "failed", detail := e }
        continue
      let t0 ← IO.monoMsNow
      let saved ← saveState
      -- the phase the generation of `f` is in, reported when it exceeds its budget
      let stage ← IO.mkRef "call lemmas of the callees"
      let (rep, newCall) ← tryCatchRuntimeEx (withCurrHeartbeats do
        let mut newCall := false
        let preE ← mkListLit extFnTy (pre.map fnE)
        let bi ← mkAppM ``Hax.Ascent.extBuiltins #[T, preE]
        let st0 : StCtx := {
          stTy := mkConst ``Unit
          vars := #[]
          proj := (fun _ => pure #[])
          stVal := mkConst ``Unit.unit }
        -- the call lemmas of the callees, specialized to this prefix
        let mut idxF := idx
        for g in ((callsOf.getD f []) ++ (globalsOf.getD f [])).eraseDups do
          let lem := Name.str (ns ++ `HaxCall) g
          unless (← getEnv).contains lem do continue
          let some jg := pre.idxOf? g | continue
          let postG := (pre.drop (jg + 1)).map fnE
          let postE ← mkListLit extFnTy postG
          let c := mkConst lem
          let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType c) (some (insts.size + 2))
          for m in mvs, i in insts do
            unless ← isDefEq m i do throwError "hax_ascend: internal: call lemma instance"
          unless ← isDefEq mvs[insts.size]! postE do throwError "hax_ascend: internal: call lemma"
          let fresh ← instantiateMVars (← inferType mvs[insts.size + 1]!)
          mvs[insts.size + 1]!.mvarId!.assign (← proveDecide fresh)
          let spec ← instantiateMVars (mkAppN c mvs)
          let auxN := gen f ++ Name.mkSimple s!"call_{g}"
          addThm auxN (← mkForallFVars insts (← inferType spec)) (← mkLambdaFVars insts spec)
          idxF := idxF.insert g #[auxN]
        let tSpec ← IO.monoMsNow
        stage.set "globals"
        let ctx0 : GCtx := { bi := bi, st := st0, leaves := idxF, hints := {} }
        let mut globals := []
        for g in globalsOf.getD f [] do
          let some (pf, sv) ← (matchLeaf g #[] none false).run ctx0
            | throwError "global: {g}"
          globals := globals ++ [(g, sv, pf)]
        let gv := mkBList (globals.map fun (g, sv, _) => (g, sv))
        let mut chain ← mkAppM ``Hax.Ascent.map_global_nil #[bi]
        for (_, _, pf) in globals.reverse do
          chain ← mkAppM ``Hax.Ascent.map_global_cons #[pf, chain]
        let hgv ← mkAppOptM ``Hax.Ascent.globalVals_of_map #[bi, fnE f, gv, chain]
        let surE ← applyInsts sur insts
        let hints := match (← getConstInfo sur).value? with
          | some v => letTypes v {}
          | none => {}
        let hints ← hints.foldM (init := ({} : Std.HashMap String Expr)) fun m k t => do
          return m.insert k (← normTy t)
        let spec : FnSpec := {
          lit := (← applyInsts infos[f]!.2.1 insts), surface := surE, params := params.getD f [],
          globals, bi, leaves := idxF, hints, normTy
          entry := fun A _ => do
            let tys ← forallTelescopeReducing (← inferType surE) fun xs _ => do
              let xs ← xs.filterM fun (x : Expr) => return !(← x.fvarId!.getBinderInfo).isInstImplicit
              xs.toList.mapM fun x => do normTy (← inferType x)
            let vsOf (a : Expr) : MetaM Expr := do
              let cs ← argComps a tys.length
              mkListLit valTy (← (cs.zip tys).mapM fun (c, t) => mkEnc t c)
            let entry ← withLocalDeclD `a A fun a => do
              mkLambdaFVars #[a] (← mkAppM ``Hax.Ascent.ExtFn.entry #[bi, fnE f, ← vsOf a])
            let hentry ← withLocalDeclD `a A fun a => withLocalDeclD `h (mkConst ``True) fun h => do
              mkLambdaFVars #[a, h] (← mkAppM ``Hax.Ascent.binds_entry #[hgv, ← vsOf a])
            return (entry, hentry) }
        let tGen0 ← IO.monoMsNow
        stage.set "generation"
        let res ← ascendFn spec
        let tGen ← IO.monoMsNow
        stage.set "declarations"
        -- declarations
        let genN := gen f ++ `gen
        addDefn genN (← mkForallFVars insts (← inferType res.fn)) (← mkLambdaFVars insts res.fn)
        let genApp := mkAppN (mkConst genN) insts
        let thmTy := res.thmTy.replace fun e => if e == res.fn then some genApp else none
        addThm (gen f ++ `corres) (← mkForallFVars insts thmTy)
          (← mkLambdaFVars insts (← mkExpectedTypeHint res.thm thmTy))
        let mut valFn := genApp
        if let some m := res.merged? then
          addDefn (gen f ++ `merged) (← mkForallFVars insts (← inferType m)) (← mkLambdaFVars insts m)
          valFn := mkAppN (mkConst (gen f ++ `merged)) insts
        let mut oracle := "mismatch"
        if res.oracle then
          let oty ← withLocalDeclD `a res.argTy fun a => do
            mkForallFVars #[a] (← mkEq (mkApp valFn a) (res.surfaceFn.beta #[a]))
          let opf ← withLocalDeclD `a res.argTy fun a => do
            mkLambdaFVars #[a] (← mkEqRefl (mkApp valFn a))
          try
            addThm (gen f ++ `oracle) (← mkForallFVars insts oty)
              (← mkLambdaFVars insts (← mkExpectedTypeHint opf oty))
            oracle := "rfl"
          catch _ => oracle := "mismatch (kernel)"
        -- the call lemma
        let tDecl ← IO.monoMsNow
        let mut callNote := ""
        if rtNames.contains f || isTagged f || tableNames.contains f then
          callNote := "no call lemma: the name is taken by the runtime or the struct table"
        else
          let callRes ← budgeted do
            withLocalDeclD `post fnsTy fun post => do
              let freshTy := mkNot (← mkAppM ``Membership.mem
                #[← mkAppM ``List.map #[mkConst ``Hax.Ascent.ExtFn.name, post], mkStrLit f])
              withLocalDeclD `hfresh freshTy fun hfresh => do
                let tys ← forallTelescopeReducing (← inferType surE) fun xs _ => do
                  let xs ← xs.filterM fun (x : Expr) => return !(← x.fvarId!.getBinderInfo).isInstImplicit
                  xs.toList.mapM fun x => do normTy (← inferType x)
                let decls ← tys.toArray.mapIdxM fun i t => pure (Name.mkSimple s!"x{i}", t)
                withLocalDeclsDND decls fun xs => do
                  let aT ← mkArgTuple xs.toList
                  -- the guard of the correspondence, a hypothesis of the call lemma
                  let gTy := (res.guard.beta #[aT]).headBeta
                  let withGuard (k : Array Expr → MetaM Unit) : MetaM Unit :=
                    if gTy.isConstOf ``True then k #[]
                    else withLocalDeclD `hG gTy fun h => k #[h]
                  withGuard fun hGs => do
                  let r ← rapp (if res.merged?.isSome then ``Hax.Ascent.extBuiltins_callX
                    else ``Hax.Ascent.extBuiltins_call)
                  r.set `T T; r.set `pre preE; r.set `post post; r.set `fn (fnE f)
                  r.set `a aT
                  -- the argument encoding of a struct of many fields, assembled by parts
                  for m in r.mvs, b in r.bis do
                    let m' ← instantiateMVars m
                    unless b.isInstImplicit && m'.isMVar do continue
                    let cls ← instantiateMVars (← inferType m')
                    if cls.isAppOf ``Hax.Ascent.HaxArgs && !cls.hasExprMVar then
                      discard <| isDefEq m' (← synthLarge cls)
                  r.set `h (mkAppN (mkConst (gen f ++ `corres)) insts)
                  r.set `hfresh hfresh
                  r.set `hG (hGs[0]?.getD (mkConst ``True.intro))
                  r.side `hrt; r.side `htag; r.side `hT; r.side `hlen
                  let pf0 ← r.done
                  let vs ← mkListLit valTy (← (xs.toList.zip tys).mapM fun (x, t) => mkEnc t x)
                  let lhs := mkApp2 (← mkAppM ``Hax.Ascent.extBuiltins
                    #[T, ← mkAppM ``HAppend.hAppend #[preE, ← mkAppM ``List.cons #[fnE f, post]]])
                    (mkStrLit f) vs
                  let β ← inferType (mkApp valFn aT)
                  let rhs ← mkAppM ``Option.some #[← mkEnc β (mkApp valFn aT)]
                  let ty ← mkEq lhs rhs
                  let pf ← match res.parts? with
                    | some (C, w, v) => do
                      let some (_, _, r0) := (← inferType pf0).eq? | throwError "no"
                      let e ← mkAppM ``Hax.Ascent.mergeExcept_ite
                        #[C.beta #[aT], w.beta #[aT], v.beta #[aT]]
                      let g ← withLocalDeclD `x β fun x => do
                        mkLambdaFVars #[x] (← mkAppM ``Option.some #[← mkEnc β x])
                      let c ← mkCongrArg g e
                      mkEqTrans pf0 (← mkExpectedTypeHint c (← mkEq r0 rhs))
                    | none => pure pf0
                  addThm (Name.str (ns ++ `HaxCall) f)
                    (← mkForallFVars (insts ++ #[post, hfresh] ++ xs ++ hGs) ty)
                    (← mkLambdaFVars (insts ++ #[post, hfresh] ++ xs ++ hGs)
                      (← mkExpectedTypeHint pf ty))
          match callRes with
          | .ok () => newCall := true
          | .error e => callNote := s!"no call lemma: {e}"
        -- the correspondence under the whole table, under a budget of its own
        let tCall ← IO.monoMsNow
        stage.set "correspondence under the whole table"
        withCurrHeartbeats do
          let post := order.toList.drop (k - 1)
          let postE ← mkListLit extFnTy (post.map fnE)
          let bodyE ← applyInsts infos[f]!.2.1 insts
          let heTy ← mkEq (← mkAppM ``Hax.Ascent.callsOK
            #[← mkAppM ``Hax.Ascent.notIn #[postE], bodyE]) trueE
          let he ← mkExpectedTypeHint (← mkEqRefl trueE) heTy
          let ext ← mkAppOptM (if res.parts?.isSome then ``Hax.Ascent.fnCorresX_extend
              else ``Hax.Ascent.fnCorres_extend)
            #[T, preE, postE, none, he]
          let full ← mkAppM' ext #[mkAppN (mkConst (gen f ++ `corres)) insts]
          let fullTy ← inferType full
          let allE := mkAppN (mkConst (gen "fns")) insts
          let fullTy := fullTy.replace fun e =>
            if e.isAppOfArity ``HAppend.hAppend 6 && e.appFn!.appArg! == preE then some allE else none
          addThm (gen f ++ `corres_full) (← mkForallFVars insts fullTy)
            (← mkLambdaFVars insts (← mkExpectedTypeHint full fullTy))
          let t1 ← IO.monoMsNow
          let kind := if res.merged?.isSome then "proved (early return)" else "proved"
          let phases := s!" [spec {tSpec - t0}, pre {tGen0 - tSpec}, gen {tGen - tGen0}, decl {tDecl - tGen}, call {tCall - tDecl}, full {t1 - tCall}]"
          let detail := s!"oracle {oracle}" ++ phases ++ (if callNote.isEmpty then "" else s!"; {callNote}") ++
            (if census.isEmpty then "" else s!"; unused constructs {census}")
          let rep : FnReport := { name := f, status := kind, ms := t1 - t0, detail := detail }
          pure (rep, newCall)) fun ex => do
        saved.restore
        let t1 ← IO.monoMsNow
        let msg := (← msgStr ex).replace "\n" " "
        let phase ← stage.get
        let (status, msg) := if ex.isRuntime then ("timeout", s!"budget exceeded in {phase}: {msg}")
          else ("failed", msg)
        let detail := msg ++ (if census.isEmpty then "" else s!"; constructs {census}")
        let rep : FnReport := { name := f, status, ms := t1 - t0, detail := detail }
        pure (rep, false)
      reports := reports.push rep
      if newCall then
        idx := idx.insert f ((idx.getD f #[]).push (Name.str (ns ++ `HaxCall) f))
    return (reports, notes)
  if hasCls then
    withLocalDecl `inst .instImplicit (mkConst clsName) fun i => body #[i]
  else body #[]

/-- A tab-separated line of a report: module, namespace, function, result, time in
    milliseconds, detail. -/
def FnReport.toTSV (modName ns : Name) (r : FnReport) : String :=
  "\t".intercalate [toString modName, toString ns, r.name, r.status, toString r.ms,
    r.detail.replace "\t" " "]

/-- Import this module and the extraction module `modName`, run the generator on the
    extraction namespace `ns`, and return its report lines and notes. The environment is
    discarded afterwards; the run elaborates the generated declarations but writes no
    file. -/
def coverageRun (modName ns : Name) (heartbeats : Nat := 200000) :
    IO (Array String × Array String) := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `CatCrypt.Hax.Ascent.Coverage }, { module := modName }]
    {} (loadExts := true)
  let ctx : Core.Context := {
    fileName := s!"<hax-coverage {modName}>"
    fileMap := default
    maxHeartbeats := heartbeats * 1000 }
  let st : Core.State := { env }
  let run : CoreM (Array FnReport × Array String) :=
    ((ascendExtraction ns none).run' {} {}).run' {} {}
  let ((reports, notes), _) ← run.toIO ctx st
  return (reports.map (FnReport.toTSV modName ns), notes)

end Hax.Ascent.Gen

open Lean Meta Elab Command Term in
/-- `#hax_coverage Ns` runs the generator on every literal of the extraction `Ns`,
    declares the results, and reports per function whether its correspondence was
    proved, with the oracle status, or the construct or leaf that stopped it. String
    arguments restrict the run to the named functions. -/
elab "#hax_coverage " ns:ident sel:(str)* : command => do
  let sel := if sel.isEmpty then none else some (sel.toList.map (·.getString))
  let (reports, notes) ← liftTermElabM <|
    Hax.Ascent.Gen.ascendExtraction ns.getId sel
  let proved := (reports.filter (·.status.startsWith "proved")).size
  let lines := reports.toList.map fun r => s!"| {r.name} | {r.status} | {r.ms} | {r.detail} |"
  logInfo m!"{ns.getId}: {proved}/{reports.size} proved\n| function | result | ms | detail |\n|---|---|---|---|\n{"\n".intercalate lines}\nnotes:\n{"\n".intercalate notes.toList}"

open Lean Meta Elab Command Term in
/-- `hax_ascend Ns` runs the generator on every literal of the extraction `Ns` and
    declares the results; it reports the number of functions proved. -/
elab "hax_ascend " ns:ident : command => do
  let (reports, _) ← liftTermElabM <| Hax.Ascent.Gen.ascendExtraction ns.getId none
  let proved := (reports.filter (·.status.startsWith "proved")).size
  logInfo m!"{ns.getId}: {proved}/{reports.size} functions proved"

end

end
