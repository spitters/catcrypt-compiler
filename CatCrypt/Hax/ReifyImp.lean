/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Generate
public import CatCrypt.Crypto.Hax.ImpRustPrint
public meta import Lean

/-!
# A reifier from pure Lean into `ImpExpr`, validated by the ascent generator

`reifyImp% n f` reads the body of the definition `f` and returns the `ImpExpr` literal of
its last `n` explicit parameters. The binders of `f` are classified as follows: type
binders and instance binders are skipped, the last `n` remaining binders are the program
parameters (read as variables), and the binders before them are the named operations (read
as builtin calls named by the binder).

The fragment:

* nested `let` (and `have`), each bound name made unique by a numeric suffix;
* an application of an operation binder to arguments, read as `.app name args`, and an
  operation binder of non-function type, read as the constant call `.app name []`;
* a right-nested `Prod.mk`, read as one flat `.tuple`, matching the flat encoding
  `HaxTupleEnc`;
* `Prod.fst (Prod.snd^k x)`, and `Prod.snd^k x` at the last component of `x`, read as
  `.proj x k`;
* `if c then a else b` and `cond c a b`, with the condition a Bool term (`b = true`,
  `decide p`) or an `Int` comparison (`<`, `≤`, `=`, read as the calls `lt`, `le`, `eq`);
* the Boolean connectives `!`, `&&`, `||`, and `¬`, `∧`, `∨` in a condition or under
  `decide`, read as the calls `Not`, `&&`, `||` on both operands: the call names of the
  hax extraction of Rust `!`, `&&`, `||` on `bool`, which the front's call typing
  (`hax64BitTable`) types on bits;
* `some x` and `none`, read as the calls `Some` and `None` of the constructors of the
  hax value `.option`;
* `Int` and `Bool` literals, an integer literal in any of the forms a closed integer term
  takes after `Meta.reduce`: `Int.ofNat k`, `Int.negSucc k`, the cast `((k : Nat) : Int)`
  of a closed numeral and a negation (`intLit?`).

The output is in A-normal form: every operand of a call, a projection, a tuple or a
conditional is a variable, a compound operand is bound by a `let` to a fresh name, and the
tail is a variable, a tuple of variables or a conditional. This is the form the Rust
printer `Crypto.Hax.ppImpRustFnRet` accepts.

No correctness theorem covers the reifier. Each output is validated instead by the
tactic `ascend_reified`, which runs the ascent generator `Hax.Ascent.Gen.ascendFn` on the
literal, the builtin table and its leaf lemmas, and closes a goal
`FnCorres bi e entry (fun _ => True) f` when the generated statement is definitionally
the goal; the obligation `G = f` is discharged by that definitional check.

## Main definitions

* `reifyImp%` — the reifier; `reifyImp% n f unfolding [g, …]` first unfolds the
  applications of `g, …` in the body (`unfoldNamed`), so that a definition by recursion on
  a closed argument (a list literal) is read as the term it reduces to;
  `reducing [h, …] within N` replaces each closed application of `h, …` by its normal form
  under `Meta.reduce`, of at most `N` subterm objects (`reduceClosed`)
* `ascend_reified` — the validation tactic
* `edBi` — the builtin table of the field operations of the pilot
* `edwardsAddLean`, `edwardsAddImp` — the extended-coordinates addition of
  `Ristretto255.element_add` over named field operations, and its literal
* `condNegLean`, `condNegImp` — a conditional negation, and its literal
* `cmpBi` — the builtin table of the `Int` comparison `lt` and the connectives
* `bandCondLean`, `propCondLean` — conditions with connectives on Bool and under `decide`
* `foldAddL`, `sumThreeLean`, `sumThreeImp` — a fold over a list literal, and its literal
* `closedConstLean`, `closedConstImp` — additions of constants given by closed terms, and
  the literal read after `reducing`
* `PilotCode`, `PilotCode.blocks`, `pilotResume`, `pilotFold`, `pilotCode`, `codeRunLean`,
  `codeRunImp` — a fold over the blocks of a closed code tree, each block read by a match
  with a catch-all arm (a sparse `casesOn`), and its literal
* `pilotCodeL`, `pilotStepL`, `pilotFoldL`, `codeRunLLean`, `codeRunLImp` — a fold over the
  blocks of a closed code tree computed over `40` positions, and its literal

## Main results

* `edwardsAddImp_eq` — the literal of the pilot, stated in full
* `edwardsAdd_fnCorres` — the literal of the pilot denotes `edwardsAddLean`
* `edwardsAdd_prints` — the literal of the pilot prints as a Rust function
* `condNeg_fnCorres` — the literal of the conditional negation denotes `condNegLean`
* `bandCond_fnCorres`, `propCond_fnCorres` — the literals with the calls `&&`, `||`, `Not`
  denote `bandCondLean` and `propCondLean`
* `sumThree_fnCorres` — the literal of a fold over a list literal, read after `unfolding`,
  denotes `sumThreeLean`
* `closedConst_fnCorres` — the literal with the integer literals of reduced closed terms
  denotes `closedConstLean`
* `codeRun_fnCorres` — the literal of the fold over the blocks of a code tree, with the
  matches over the reduced blocks reduced, denotes `codeRunLean`
* `codeRunL_fnCorres` — the literal of `codeRunLLean` denotes it, the goal compared over
  its function reduced by the clauses of the literal (`ascend_reified … unfolding …
  reducing …`)
-/

@[expose] public section

set_option autoImplicit false

meta section

open Lean Meta Elab Term Tactic

namespace CatCrypt.Hax.ReifyImp

/-- The reifier context: the variable name of each program parameter and `let` binder,
    and the builtin name of each operation binder. -/
structure Ctx where
  /-- Program parameters and `let` binders. -/
  vars : Std.HashMap FVarId String := {}
  /-- Operation binders. -/
  ops : Std.HashMap FVarId String := {}

/-- The reifier monad, with the names taken as state. -/
abbrev ReifyM := StateRefT (List String) MetaM

/-- The string of a binder name, without macro scopes. -/
def nameStr (n : Name) : String :=
  match n.eraseMacroScopes with
  | .str _ s => s
  | _ => "x"

/-- A name not among `used`: `base`, or `base_k` for the least `k` that is free. -/
def freshName (used : List String) (base : String) : String := Id.run do
  if !used.contains base then return base
  let mut k := 1
  while used.contains s!"{base}_{k}" do k := k + 1
  return s!"{base}_{k}"

/-- A name not taken, `freshName` of `base`, recorded as taken. -/
def fresh (base : String) : ReifyM String := do
  let s := freshName (← get) base
  modify (s :: ·)
  return s

/-- `ImpExpr.letBind x₁ v₁ (… (ImpExpr.letBind xₖ vₖ b))` for the bindings `(xᵢ, vᵢ)`. -/
def wrapLets (bs : List (String × Expr)) (b : Expr) : Expr :=
  bs.foldr (fun (x, v) acc => mkApp3 (mkConst ``Hax.ImpExpr.letBind) (mkStrLit x) v acc) b

/-- `ImpExpr.var x`. -/
def mkVar (x : String) : Expr := mkApp (mkConst ``Hax.ImpExpr.var) (mkStrLit x)

/-- `ImpExpr.app f args`. -/
def mkCall (f : String) (args : List Expr) : MetaM Expr := do
  return mkApp2 (mkConst ``Hax.ImpExpr.app) (mkStrLit f)
    (← mkListLit (mkConst ``Hax.ImpExpr) args)

/-- The number of components of the flat tuple encoding of `ty`: one more than that of
    `β` for `ty = α × β`, and `1` otherwise. -/
partial def tupleArity (ty : Expr) : MetaM Nat := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFnArgs with
  | (``Prod, #[_, β]) => return 1 + (← tupleArity β)
  | _ => return 1

/-- A second projection `Prod.snd x` or `x.2`, and its argument. -/
def sndArg? (e : Expr) : Option Expr :=
  match e with
  | .proj ``Prod 1 x => some x
  | _ => if e.isAppOfArity ``Prod.snd 3 then some e.appArg! else none

/-- A first projection `Prod.fst x` or `x.1`, and its argument. -/
def fstArg? (e : Expr) : Option Expr :=
  match e with
  | .proj ``Prod 0 x => some x
  | _ => if e.isAppOfArity ``Prod.fst 3 then some e.appArg! else none

/-- The base of a chain of second projections and its length. -/
partial def sndChain (e : Expr) : Expr × Nat :=
  match sndArg? e with
  | some x => let (b, k) := sndChain x; (b, k + 1)
  | none => (e, 0)

/-- The components of a right-nested `Prod.mk`. -/
partial def tupleElems (e : Expr) : List Expr :=
  if e.isAppOfArity ``Prod.mk 4 then
    e.getArg! 2 :: tupleElems (e.getArg! 3)
  else [e]

/-- The bindings of a right-hand side followed by a variable: the right-hand side itself
    when it is a variable, and otherwise a fresh name bound to it, named `x{k}` for the
    projection `.proj (.var x) k` and `t` for the others. -/
def atomize (p : List (String × Expr) × Expr) : ReifyM (List (String × Expr) × Expr) := do
  let (bs, r) := p
  if r.isAppOfArity ``Hax.ImpExpr.var 1 then return (bs, r)
  let base : String := Id.run do
    if r.isAppOfArity ``Hax.ImpExpr.proj 2 then
      let a := r.getArg! 0
      if a.isAppOfArity ``Hax.ImpExpr.var 1 then
        if let .lit (.strVal x) := a.appArg! then
          if let some k := (r.getArg! 1).nat? then return s!"{x}{k}"
    return "t"
  let t ← fresh base
  return (bs ++ [(t, r)], mkVar t)

/-- The value of a closed natural numeral: a raw literal, `OfNat.ofNat` of one, or a closed
    term of `Nat.succ`, `+`, `*` and `-` on such numerals (`Meta.evalNat`). -/
def natLit? (e : Expr) : MetaM (Option Nat) := do
  if e.hasFVar || e.hasMVar then return none
  if let some k := e.rawNatLit? then return some k
  (evalNat e).run

/-- The value of an integer literal: `OfNat.ofNat` of a raw literal at `Int`, `Int.ofNat k`
    and the cast `((k : Nat) : Int)` of a closed numeral `k` (`natLit?`), `Int.negSucc k`, and
    the negation of an integer literal. These are the forms a closed integer term takes after
    `Meta.reduce`. -/
partial def intLit? (e : Expr) : MetaM (Option Int) := do
  let isInt (t : Expr) : MetaM Bool := return (← whnfR t).isConstOf ``Int
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if ← isInt (e.getArg! 0) then
      if let some k := (e.getArg! 1).rawNatLit? then return some (Int.ofNat k)
    return none
  if e.isAppOfArity ``Int.ofNat 1 then
    return (← natLit? e.appArg!).map Int.ofNat
  if e.isAppOfArity ``Int.negSucc 1 then
    return (← natLit? e.appArg!).map Int.negSucc
  if e.isAppOfArity ``Nat.cast 3 || e.isAppOfArity ``NatCast.natCast 3 then
    if ← isInt (e.getArg! 0) then return (← natLit? e.appArg!).map Int.ofNat
    return none
  if e.isAppOfArity ``Neg.neg 3 then
    if ← isInt (e.getArg! 0) then return (← intLit? e.appArg!).map (- ·)
  return none

mutual

/-- The A-normal literal of a term of the fragment in tail position: bindings followed by
    a variable, a tuple of variables or a conditional on a variable. -/
partial def reify (ctx : Ctx) (e : Expr) : ReifyM Expr := do
  let e := (← instantiateMVars e).headBeta
  match e with
  | .mdata _ b => reify ctx b
  | .letE n t v b _ => do
    let (bs, rv) ← reifyRhs ctx v
    withLetDecl n t v fun x => do
      let s ← fresh (nameStr n)
      let bE ← reify { ctx with vars := ctx.vars.insert x.fvarId! s } (b.instantiate1 x)
      return wrapLets (bs ++ [(s, rv)]) bE
  | _ => do
    let (bs, r) ← reifyRhs ctx e
    if r.isAppOfArity ``Hax.ImpExpr.var 1 || r.isAppOfArity ``Hax.ImpExpr.tuple 1 ||
        r.isAppOfArity ``Hax.ImpExpr.ifThenElse 3 then
      return wrapLets bs r
    let (bs, r) ← atomize (bs, r)
    return wrapLets bs r

/-- The literal of a term of the fragment as bindings followed by a right-hand side: a
    variable, a call on variables, a projection of a variable, a tuple of variables, a
    literal, or a conditional on a variable with branches in tail position. -/
partial def reifyRhs (ctx : Ctx) (e : Expr) : ReifyM (List (String × Expr) × Expr) := do
  let e := (← instantiateMVars e).headBeta
  match e with
  | .mdata _ b => reifyRhs ctx b
  | .letE n t v b _ => do
    let (bs, rv) ← reifyRhs ctx v
    withLetDecl n t v fun x => do
      let s ← fresh (nameStr n)
      let (bs', rb) ← reifyRhs { ctx with vars := ctx.vars.insert x.fvarId! s }
        (b.instantiate1 x)
      return (bs ++ [(s, rv)] ++ bs', rb)
  | .fvar id => do
    if let some s := ctx.vars[id]? then return ([], mkVar s)
    if let some s := ctx.ops[id]? then return ([], ← mkCall s [])
    throwError "reifyImp: free variable {e} is neither a parameter, a let nor an operation"
  | _ => do
    if let some x := fstArg? e then
      let (b, k) := sndChain x
      let (bs, a) ← reifyAtom ctx b
      return (bs, mkApp2 (mkConst ``Hax.ImpExpr.proj) a (mkNatLit k))
    if (sndArg? e).isSome then
      let (b, k) := sndChain e
      let n ← tupleArity (← inferType b)
      unless n = k + 1 do
        throwError "reifyImp: projection onto a sub-tuple: {e}"
      let (bs, a) ← reifyAtom ctx b
      return (bs, mkApp2 (mkConst ``Hax.ImpExpr.proj) a (mkNatLit k))
    if e.isAppOfArity ``Prod.mk 4 then
      let (bs, as) ← reifyAtoms ctx (tupleElems e)
      return (bs, mkApp (mkConst ``Hax.ImpExpr.tuple) (← mkListLit (mkConst ``Hax.ImpExpr) as))
    if e.isAppOfArity ``ite 5 then
      let (bs, c) ← atomize (← reifyCond ctx (e.getArg! 1))
      return (bs, mkApp3 (mkConst ``Hax.ImpExpr.ifThenElse) c (← reify ctx (e.getArg! 3))
        (← reify ctx (e.getArg! 4)))
    if e.isAppOfArity ``cond 4 then
      let (bs, c) ← reifyAtom ctx (e.getArg! 1)
      return (bs, mkApp3 (mkConst ``Hax.ImpExpr.ifThenElse) c (← reify ctx (e.getArg! 2))
        (← reify ctx (e.getArg! 3)))
    if e.isAppOfArity ``Option.some 2 then
      let (bs, as) ← reifyAtoms ctx [e.appArg!]
      return (bs, ← mkCall "Some" as)
    if e.isAppOfArity ``Option.none 1 then return ([], ← mkCall "None" [])
    if e.isConstOf ``Bool.true || e.isConstOf ``Bool.false then
      return ([], mkApp (mkConst ``Hax.ImpExpr.lit) (mkApp (mkConst ``Hax.ImpLit.bool) e))
    if let some k ← intLit? e then
      return ([], mkApp (mkConst ``Hax.ImpExpr.lit) (mkApp (mkConst ``Hax.ImpLit.int) (toExpr k)))
    if e.isAppOfArity ``not 1 then
      let (bs, as) ← reifyAtoms ctx [e.appArg!]
      return (bs, ← mkCall "Not" as)
    if e.isAppOfArity ``and 2 then
      let (bs, as) ← reifyAtoms ctx [e.getArg! 0, e.getArg! 1]
      return (bs, ← mkCall "&&" as)
    if e.isAppOfArity ``or 2 then
      let (bs, as) ← reifyAtoms ctx [e.getArg! 0, e.getArg! 1]
      return (bs, ← mkCall "||" as)
    if e.isAppOfArity ``Decidable.decide 2 then return ← reifyCond ctx (e.getArg! 0)
    if let .fvar id := e.getAppFn then
      if let some s := ctx.ops[id]? then
        let (bs, as) ← reifyAtoms ctx e.getAppArgs.toList
        return (bs, ← mkCall s as)
    throwError "reifyImp: term outside the fragment: {e}"

/-- The literal of a term of the fragment as bindings followed by a variable. -/
partial def reifyAtom (ctx : Ctx) (e : Expr) : ReifyM (List (String × Expr) × Expr) := do
  atomize (← reifyRhs ctx e)

/-- The literals of terms of the fragment as bindings followed by variables, the bindings
    of the terms in order. -/
partial def reifyAtoms (ctx : Ctx) (es : List Expr) :
    ReifyM (List (String × Expr) × List Expr) := do
  let mut bs : List (String × Expr) := []
  let mut as : List Expr := []
  for e in es do
    let (b, a) ← reifyAtom ctx e
    bs := bs ++ b
    as := as ++ [a]
  return (bs, as)

/-- The literal of a condition as bindings followed by a right-hand side: a Bool term
    compared with `true`, a negation, a conjunction or disjunction of conditions, or an
    `Int` comparison. -/
partial def reifyCond (ctx : Ctx) (p : Expr) : ReifyM (List (String × Expr) × Expr) := do
  let p := (← instantiateMVars p).headBeta
  if p.isAppOfArity ``Eq 3 then
    if (p.getArg! 2).isConstOf ``Bool.true then return ← reifyRhs ctx (p.getArg! 1)
    let (bs, as) ← reifyAtoms ctx [p.getArg! 1, p.getArg! 2]
    return (bs, ← mkCall "eq" as)
  if p.isAppOfArity ``LT.lt 4 then
    let (bs, as) ← reifyAtoms ctx [p.getArg! 2, p.getArg! 3]
    return (bs, ← mkCall "lt" as)
  if p.isAppOfArity ``LE.le 4 then
    let (bs, as) ← reifyAtoms ctx [p.getArg! 2, p.getArg! 3]
    return (bs, ← mkCall "le" as)
  if p.isAppOfArity ``Not 1 then
    let (bs, a) ← atomize (← reifyCond ctx p.appArg!)
    return (bs, ← mkCall "Not" [a])
  if p.isAppOfArity ``And 2 || p.isAppOfArity ``Or 2 then
    let (bs, a) ← atomize (← reifyCond ctx (p.getArg! 0))
    let (bs', b) ← atomize (← reifyCond ctx (p.getArg! 1))
    return (bs ++ bs', ← mkCall (if p.isAppOfArity ``And 2 then "&&" else "||") [a, b])
  throwError "reifyImp: condition outside the fragment: {p}"

end

/-- The weak head normal form of `e` as `whnf` computes it (`whnfCore`, the `Nat` literal
    operations `reduceNat?` and delta steps `unfoldDefinition?` at the
    ambient transparency, until none applies), each delta step counted by `tick`. -/
partial def whnfTicked (tick : MetaM Unit) (e : Expr) : MetaM Expr := do
  let e' ← whnfCore e
  if let some v ← reduceNat? e' then return v
  let some e'' ← unfoldDefinition? e' | return e'
  tick
  whnfTicked tick e''

/-- The state shared by the closed reductions of one run of `unfoldNamed`: the normal form of
    each term already reduced, and the step counter of the run. -/
structure ReduceCtx where
  /-- The normal form of each reduced term. -/
  cache : IO.Ref (Std.HashMap Expr Expr)
  /-- Counts one step; an error once the steps exceed the fuel of the run. -/
  tick : MetaM Unit

/-- The normal form of `e` under `Meta.reduce` (explicit arguments only, types and proofs
    skipped), computed by the same traversal: the weak head normal form (`whnfTicked`), then
    the head and the explicit arguments of an application, the body of a binder and the
    structure of a projection reduced in turn. A term already reduced is read from the cache
    of `rc`; each term reduced anew counts one step (`rc.tick`); each result is passed to
    `count`. -/
partial def reduceVisit (rc : ReduceCtx) (count : Expr → MetaM Unit) (e : Expr) :
    MetaM Expr := do
  if let some r := (← rc.cache.get)[e]? then
    count r
    return r
  rc.tick
  let r ← Core.withIncRecDepth do
    if ← isType e then return e
    if ← isProof e then return e
    let w ← whnfTicked rc.tick e
    match w with
    | .app .. =>
      let f ← reduceVisit rc count w.getAppFn
      let finfo ← getFunInfoNArgs f w.getAppNumArgs
      let mut args := w.getAppArgs
      for i in [0:args.size] do
        if h : i < finfo.paramInfo.size then
          if finfo.paramInfo[i].isExplicit then
            args ← args.modifyM i (reduceVisit rc count)
        else
          args ← args.modifyM i (reduceVisit rc count)
      if f.isConstOf ``Nat.succ && args.size == 1 && args[0]!.isRawNatLit then
        return mkRawNatLit (args[0]!.rawNatLit?.get! + 1)
      return mkAppN f args
    | .lam .. => lambdaTelescope w fun xs b => do mkLambdaFVars xs (← reduceVisit rc count b)
    | .forallE .. =>
      forallTelescope w fun xs b => do mkForallFVars xs (← reduceVisit rc count b)
    | .proj n i s => return mkProj n i (← reduceVisit rc count s)
    | _ => return w
  rc.cache.modify (·.insert e r)
  count r
  return r

/-- The normal form of the closed term `t` under `Meta.reduce` at default transparency
    (`reduceVisit`). Its size is the number of distinct subterm objects (`Expr.numObjs`,
    shared subterms counted once); a normal form of more than `maxSize` objects is an error
    that states the size. The bound is checked during the reduction against a lower bound
    of the size, the spine nodes of the distinct closed results reduced so far, and the
    reduction stops with an error as soon as that lower bound exceeds `maxSize`. -/
def reduceClosed (rc : ReduceCtx) (t : Expr) (maxSize : Nat) : MetaM Expr := do
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  let size ← IO.mkRef 0
  let count (r : Expr) : MetaM Unit := do
    if r.hasFVar || (← seen.get).contains r then return
    seen.modify (·.insert r)
    size.modify (· + max 1 r.getAppNumArgs)
    let n ← size.get
    if n > maxSize then
      throwError "reifyImp: the normal form of {t.getAppFn} has at least {n} subterm \
        objects, more than the bound {maxSize}"
  let r ← withTransparency .default (reduceVisit rc count t)
  let size ← r.numObjs
  if size > maxSize then
    throwError "reifyImp: the normal form of {t.getAppFn} has {size} subterm objects, \
      more than the bound {maxSize}"
  return r

/-- The prefix of the binder name of a `let` that binds a shared argument (`shareName`). -/
def shareTag : Name := `_reifyImp_share

/-- The binder name of the `let` of a shared argument for the binder `n`: the string of `n`
    under the prefix `shareTag`, so that `nameStr` reads it as the string of `n`. -/
def shareName (n : Name) : Name := .str shareTag (nameStr n)

/-- Whether `n` is the binder name of the `let` of a shared argument. -/
def isShareName (n : Name) : Bool := n.getPrefix == shareTag

/-- Whether the argument `a` of a beta-redex or of an unfolded application is bound by a
    `let` instead of substituted: `a` is not a variable, a constant, a literal, a sort or a
    binder, contains a free variable (a closed argument is left to the closed reductions),
    is not a constructor application of a type other than `Prod` (data that the reductions
    take apart), and is neither a function, a type nor a proof. -/
def shareable (a : Expr) : MetaM Bool := do
  match a.consumeMData with
  | .fvar _ | .const .. | .lit _ | .sort _ | .lam .. | .forallE .. | .bvar _ | .mvar _ =>
    return false
  | a => do
    if !a.hasFVar || a.hasLooseBVars || a.hasMVar then return false
    if let some c := a.getAppFn.constName? then
      if let some (.ctorInfo ci) := (← getEnv).find? c then
        unless ci.induct == ``Prod do return false
    let ty ← whnfR (← inferType a)
    if ty.isForall || ty.isSort then return false
    return !(← isProof a)

/-- The number of occurrences of the loose bound variable `i` in `e`, counted up to `2`
    from `acc`. -/
partial def countBVar (i : Nat) (e : Expr) (acc : Nat := 0) : Nat :=
  if acc ≥ 2 || e.looseBVarRange ≤ i then acc else
  match e with
  | .bvar j => if j == i then acc + 1 else acc
  | .app f a => countBVar i a (countBVar i f acc)
  | .lam _ t b _ | .forallE _ t b _ => countBVar (i + 1) b (countBVar i t acc)
  | .letE _ t v b _ => countBVar (i + 1) b (countBVar i v (countBVar i t acc))
  | .mdata _ b | .proj _ _ b => countBVar i b acc
  | _ => acc

/-- The body `e` of a `let` with value `v`, at `d` binders below the body's outermost level,
    with each occurrence of `v` replaced by the variable of the `let` (`.bvar d`); `vd` is
    `v` lifted over the `let` and the `d` binders. -/
partial def abstractVal (vd : Expr) (d : Nat) (e : Expr) : Expr :=
  if e == vd then .bvar d
  else if e.approxDepth < vd.approxDepth then e
  else
    let under (b : Expr) : Expr := abstractVal (vd.liftLooseBVars 0 1) (d + 1) b
    match e with
    | .app f a => e.updateApp! (abstractVal vd d f) (abstractVal vd d a)
    | .lam _ t b _ => e.updateLambdaE! (abstractVal vd d t) (under b)
    | .forallE _ t b _ => e.updateForallE! (abstractVal vd d t) (under b)
    | .letE _ t v b _ => e.updateLetE! (abstractVal vd d t) (abstractVal vd d v) (under b)
    | .mdata _ b => e.updateMData! (abstractVal vd d b)
    | .proj _ _ b => e.updateProj! (abstractVal vd d b)
    | _ => e

/-- The `let` chain `e` with each recurrence of the non-atomic value of a `let` in its body
    read as the variable of the `let` (`abstractVal`), and then each `let` of a shared argument
    (`isShareName`) whose variable occurs at most once in its body replaced by its body with
    the value substituted. -/
partial def inlineShared (e : Expr) : Expr :=
  match e with
  | .letE n t v b nd =>
    let b := inlineShared b
    let b := match v.consumeMData with
      | .fvar _ | .const .. | .lit _ | .sort _ | .bvar _ => b
      | _ => abstractVal (v.liftLooseBVars 0 1) 0 b
    if isShareName n && countBVar 0 b ≤ 1 then b.instantiate1 v else .letE n t v b nd
  | _ => e

/-- The beta-reduction of `f` applied to `args`: each argument consumed by a binder of `f`
    is substituted, or bound by a `let` named by `shareName` when it is `shareable`. -/
partial def betaShare (f : Expr) (args : List Expr) : MetaM Expr := do
  match f.consumeMData, args with
  | .lam n ty b _, a :: rest =>
    if ← shareable a then return .letE (shareName n) ty a (← betaShare b rest) false
    betaShare (b.instantiate1 a) rest
  | _, _ => return mkAppN f args.toArray

/-- `k` of `args` with each `shareable` argument replaced by a `let` variable bound to it,
    named by `shareName` of the binder name of `names` at its position, and of these
    variables. -/
partial def withShared {α : Type} (names : Array Name) (args : Array Expr)
    (k : Array Expr → Array Expr → MetaM α) (i : Nat := 0) (acc fvs : Array Expr := #[]) :
    MetaM α := do
  if h : i < args.size then
    let a := args[i]
    if ← shareable a then
      withLetDecl (shareName (names.getD i `x)) (← inferType a) a fun x =>
        withShared names args k (i + 1) (acc.push x) (fvs.push x)
    else withShared names args k (i + 1) (acc.push a) fvs
  else k acc fvs

/-- `whnfCore` without zeta-reduction of `let` expressions, so that the `let`s of shared
    arguments stay; `let` variables are still unfolded (zeta-delta), so that a match on one
    reduces. -/
def whnfCoreKeepLets (e : Expr) : MetaM Expr :=
  withConfig (fun c => { c with zeta := false }) (whnfCore e)

/-- The term `e` with every application of one of the constants `cs` unfolded by
    `unfoldDefinition?` (smart unfolding for a definition by structural recursion) and its
    head reduced by `whnfCore`, again on the result, until no application of `cs` unfolds,
    and every closed full application (no free variable, at least one argument and at least
    as many arguments as the constant has leading binders) of one of the constants `rs`
    replaced by its normal form (`reduceClosed` with the bound `maxSize`, the cache of
    normal forms shared by the run); a partial application, such as the head
    `@HAdd.hAdd ℕ ℕ ℕ instHAdd` of an application with open arguments, is not reduced, and a
    constant of `rs` without arguments is reduced only inside such an application.
    After the subterms of an application are reduced, the application is reduced again
    (bottom-up): its head beta-reduced; when it is closed, a full application of `rs`
    replaced by its normal form, an application of an instance projection unfolded
    (`unfoldProjInst?`), and a term of type `Nat` that `natLit?` evaluates replaced by its
    numeral; an application of `cs` unfolded; and an application of a matcher, a
    recursor or a `casesOn` reduced by `whnfCore` (iota) when its scrutinee has become a
    constructor application. No other constant is unfolded. More than `fuel` unfoldings and
    reductions, the steps of `reduceClosed` included, is an error.

    Arguments are shared: an argument of an unfolded application of `cs` (`withShared`) or
    of a beta-redex (`betaShare`) that is `shareable` is bound once by a `let` around the
    result instead of substituted into each occurrence, the `whnfCore` steps do not
    zeta-reduce these `let`s (`whnfCoreKeepLets`), and once its body is reduced each
    recurrence of the value of a `let` in its body is read as its variable and such a `let`
    whose variable occurs at most once is substituted (`inlineShared`). A fold whose step
    reads its state more than once thus yields a term linear in the number of steps. -/
def unfoldNamed (cs : Array Name) (e : Expr) (fuel : Nat := 100000) (rs : Array Name := #[])
    (maxSize : Nat := 10000) : MetaM Expr := do
  if cs.isEmpty && rs.isEmpty then return e
  let count ← IO.mkRef 0
  let tick : MetaM Unit := do
    count.modify (· + 1)
    if (← count.get) > fuel then throwError "reifyImp: more than {fuel} unfoldings"
  let unfold? (t : Expr) : MetaM (Option Expr) := do
    let some c := t.getAppFn.constName? | return none
    unless cs.contains c do return none
    withShared (← getConstInfo c).type.getForallBinderNames.toArray t.getAppArgs fun args fvs => do
      let some t' ← unfoldDefinition? (mkAppN t.getAppFn args) | return none
      tick
      return some (← mkLetFVars fvs (← whnfCoreKeepLets t'))
  let rc : ReduceCtx := { cache := ← IO.mkRef {}, tick }
  let closed (t : Expr) : Bool := !t.hasFVar && !t.hasMVar
  let fullRs (t : Expr) : MetaM Bool := do
    unless t.isApp do return false
    let some c := t.getAppFn.constName? | return false
    unless rs.contains c do return false
    return (← getConstInfo c).type.getForallArity ≤ t.getAppNumArgs
  let fold? (t : Expr) : MetaM (Option (TransformStep)) := do
    if !closed t || !t.isApp || t.nat?.isSome then return none
    if ← fullRs t then return some (.done (← reduceClosed rc t maxSize))
    if t.getAppFn.isProj then
      if let some t' ← unfoldProjInst? t then return some (.visit t')
    unless (← whnfR (← inferType t)).isConstOf ``Nat do return none
    return (← natLit? t).map (.done ∘ mkNatLit)
  Meta.transform e
    (pre := fun t => do
      if closed t && (← fullRs t) then
        return .done (← reduceClosed rc t maxSize)
      match ← unfold? t with
      | some t' => return .visit t'
      | none => return .continue)
    (post := fun t => do
      if t.isLet then return .done (inlineShared t)
      let t ← if t.getAppFn.consumeMData.isLambda then
          betaShare t.getAppFn t.getAppArgs.toList
        else pure t
      if t.isLet then return .visit t
      if let some s ← fold? t then return s
      let some c := t.getAppFn.constName? | return .done t
      if let some t' ← unfold? t then return .visit t'
      let env ← getEnv
      unless (← isMatcher c) || isRecCore env c || isAuxRecursor env c do return .done t
      let t' ← whnfCoreKeepLets t
      if t' == t then return .done t
      tick
      return .visit t')

/-- The literal of the definition `c` over its last `n` explicit parameters, the binders
    before them read as operations. The body is first reduced by `unfoldNamed cs` with the
    closed applications of `rs` reduced under the bound `maxSize`. -/
def reifyConst (c : Name) (n : Nat) (cs : Array Name := #[]) (rs : Array Name := #[])
    (maxSize : Nat := 10000) : MetaM Expr := do
  let info ← getConstInfo c
  let some v := info.value? | throwError "reifyImp: {c} has no body"
  lambdaTelescope v fun xs body => do
    let body ← unfoldNamed cs body (rs := rs) (maxSize := maxSize)
    let mut rest : Array Expr := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit then continue
      if (← whnfR d.type).isSort then continue
      rest := rest.push x
    unless n ≤ rest.size do
      throwError "reifyImp: {c} has {rest.size} parameters, fewer than {n}"
    let nOps := rest.size - n
    let mut ctx : Ctx := {}
    let mut used : List String := []
    for x in rest, i in [0:rest.size] do
      let s := freshName used (nameStr (← x.fvarId!.getUserName))
      used := s :: used
      if i < nOps then
        ctx := { ctx with ops := ctx.ops.insert x.fvarId! s }
      else
        ctx := { ctx with vars := ctx.vars.insert x.fvarId! s }
    (reify ctx body).run' used

/-- `reifyImp% n f` is the `ImpExpr` literal of the body of `f` over its last `n` explicit
    parameters; the explicit binders before them are the builtin operations, called by
    their binder names. Without `n`, every explicit binder is a parameter. With
    `unfolding [g, …]`, the applications of the constants `g, …` in the body are unfolded
    before it is read (`unfoldNamed`). With `reducing [h, …]`, each closed application of
    one of the constants `h, …` is replaced by its normal form under `Meta.reduce`, of at
    most `10000` subterm objects, or of the bound given by `within N` (`reduceClosed`). -/
syntax "reifyImp% " (num)? ident (" unfolding " "[" ident,* "]")?
  (" reducing " "[" ident,* "]")? (" within " num)? : term

elab_rules : term
  | `(reifyImp% $[$n?]? $f:ident $[unfolding [$us?,*]]? $[reducing [$rs?,*]]?
      $[within $b?]?) => do
  let c ← realizeGlobalConstNoOverloadWithInfo f
  let consts (xs? : Option (Syntax.TSepArray `ident ",")) : TermElabM (Array Name) :=
    match xs? with
    | some xs => xs.getElems.mapM fun u => realizeGlobalConstNoOverloadWithInfo u
    | none => pure #[]
  let cs ← consts us?
  let rs ← consts rs?
  let maxSize := (b?.map (·.getNat)).getD 10000
  let n ← match n? with
    | some n => pure n.getNat
    | none => do
      let v := (← getConstInfo c).value?.getD (mkConst ``Unit)
      lambdaTelescope v fun xs _ => do
        let ys ← xs.filterM fun x => do
          let d ← x.fvarId!.getDecl
          return !d.binderInfo.isInstImplicit && !(← whnfR d.type).isSort
        return ys.size
  reifyConst c n cs rs maxSize

/-- `ascend_reified s using [l₁, …]` closes a goal `FnCorres bi e entry (fun _ => True) f`
    by the ascent generator on the literal `e`, the table `bi`, the leaf lemmas `lᵢ` and
    the surface function `s`, whose explicit binder names are the parameter names of the
    literal. The entry environment is `bindParams` of the parameter bindings; the goal is
    closed when the generated statement is definitionally the goal. With `guard G`, the
    predicate `G` of the argument tuple is the precondition of the generator
    (`FnSpec.pre?`): the side conditions of the leaves are proved from its conjuncts, and
    the goal is `FnCorres bi e entry G f`. A guard given as a `def` hides its conjuncts
    from the generator, so `G` is a lambda or an `abbrev`. With `unfolding [g, …]`,
    `reducing [h, …]` and `within N`, the clauses the literal was read with, the function
    `f` of the goal is first reduced as the reifier reduced the body: the head constant of
    `s` and the constants `g, …` unfolded and the closed applications of `h, …` reduced
    (`unfoldNamed`); the generated statement is compared with the goal over that normal
    form, which is definitionally `f`.

    Under `set_option trace.ascend_reified true`, or `trace.profiler true` for the phases
    above `trace.profiler.threshold`, each phase is a trace node with its time: the reading
    of the goal (the literal, the surface, the guard, the leaves), the generator
    (`ascendFn`, the derivation with its side conditions), the normalisation of the goal's
    function, the comparison of the generated statement with the goal, and the closing
    term. -/
syntax "ascend_reified " term " using " "[" ident,* "]" (" guard " term)?
  (" unfolding " "[" ident,* "]")? (" reducing " "[" ident,* "]")? (" within " num)? : tactic

initialize registerTraceClass `ascend_reified

/-- The phase `x` of `ascend_reified` as a trace node named `phase`. -/
def ascendPhase {α : Type} (phase : String) (x : TacticM α) : TacticM α :=
  withTraceNode `ascend_reified
    (fun r => return m!"{phase}{match r with | .ok _ => "" | .error _ => " (failed)"}") x

elab_rules : tactic
  | `(tactic| ascend_reified $sur:term using [$ls,*] $[guard $g?]? $[unfolding [$us?,*]]?
      $[reducing [$rs?,*]]? $[within $b?]?) => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  unless goal.isAppOfArity ``Hax.Ascent.FnCorres 8 do
    throwError "ascend_reified: the goal is not a FnCorres statement"
  let bi := goal.getArg! 0
  let (e, surface, pre?, params, leaves) ← ascendPhase "reading the goal" do
    let e ← whnf (goal.getArg! 4)
    let surface ← instantiateMVars (← Term.elabTermAndSynthesize sur none)
    let pre? ← g?.mapM fun g => do
      let gTy ← inferType (goal.getArg! 6)
      instantiateMVars (← Term.elabTermAndSynthesize g gTy)
    let params ← forallTelescopeReducing (← inferType surface) fun xs _ => do
      let xs ← xs.filterM fun x => return !(← x.fvarId!.getBinderInfo).isInstImplicit
      xs.toList.mapM fun x => return nameStr (← x.fvarId!.getUserName)
    let lems ← ls.getElems.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
    let leaves ← Hax.Ascent.Gen.indexLeaves {} lems
    return (e, surface, pre?, params, leaves)
  let spec : Hax.Ascent.Gen.FnSpec := {
    lit := e, surface, params, globals := [], bi, leaves, hints := {}, pre?
    entry := fun A Γ₀l => do
      let entry ← withLocalDeclD `a A fun a => do
        mkLambdaFVars #[a] (← mkAppM ``Hax.Ascent.bindParams #[Γ₀l.beta #[a]])
      let hentry ← withLocalDeclD `a A fun a => withLocalDeclD `h (mkConst ``True) fun h => do
        mkLambdaFVars #[a, h] (← mkAppM ``Hax.Ascent.binds_bindParams #[Γ₀l.beta #[a]])
      return (entry, hentry) }
  let res ← ascendPhase "ascendFn" (Hax.Ascent.Gen.ascendFn spec)
  let consts (xs? : Option (Syntax.TSepArray `ident ",")) : TacticM (Array Name) :=
    match xs? with
    | some xs => xs.getElems.mapM fun u => realizeGlobalConstNoOverloadWithInfo u
    | none => pure #[]
  let cs ← consts us?
  let rs ← consts rs?
  -- the goal over its function reduced as the reifier reduced the body
  let goalN ← if cs.isEmpty && rs.isEmpty then pure goal else
    ascendPhase "normalising the goal" do
    let some hd := surface.getAppFn.constName?
      | throwError "ascend_reified: the surface{indentExpr surface}\nis not a constant application"
    let maxSize := (b?.map (·.getNat)).getD 10000
    let fN ← lambdaTelescope (goal.getArg! 7) fun xs body => do
      mkLambdaFVars xs (← unfoldNamed (cs.push hd) body (rs := rs) (maxSize := maxSize))
    pure (mkAppN goal.getAppFn (goal.getAppArgs.set! 7 fN))
  unless ← ascendPhase "comparing with the goal" (isDefEq res.thmTy goalN) do
    throwError "ascend_reified: the generated statement{indentExpr res.thmTy}\nis not the goal"
  ascendPhase "closing the goal" do
    closeMainGoal `ascend_reified
      (← if goalN == goal then pure res.thm else mkExpectedTypeHint res.thm goalN)

end CatCrypt.Hax.ReifyImp

end

namespace CatCrypt.Hax.ReifyImp

open _root_.Hax _root_.Hax.Ascent

variable {α : Type} [HaxEnc α] [HaxEnc.Inj α]

/-! ## The builtin table of the field operations -/

/-- The builtin table of the named field operations `mul`, `add`, `sub`, `double`, the
    negation `neg` and the curve constant `d`. -/
noncomputable def edBi (mul add sub : α → α → α) (double neg : α → α) (d : α) : Builtins :=
  Table.toBuiltins [("mul", leaf2 mul), ("add", leaf2 add), ("sub", leaf2 sub),
    ("double", leaf1 double), ("neg", leaf1 neg), ("d", leaf0 d)]

section Leaves

variable (mul add sub : α → α → α) (double neg : α → α) (d : α)

theorem edBi_mul (x y : α) :
    edBi mul add sub double neg d "mul" [enc x, enc y] = some (enc (mul x y)) := by
  rw [edBi, Table.toBuiltins_of_lookup rfl, leaf2_apply]

theorem edBi_add (x y : α) :
    edBi mul add sub double neg d "add" [enc x, enc y] = some (enc (add x y)) := by
  rw [edBi, Table.toBuiltins_of_lookup rfl, leaf2_apply]

theorem edBi_sub (x y : α) :
    edBi mul add sub double neg d "sub" [enc x, enc y] = some (enc (sub x y)) := by
  rw [edBi, Table.toBuiltins_of_lookup rfl, leaf2_apply]

theorem edBi_double (x : α) :
    edBi mul add sub double neg d "double" [enc x] = some (enc (double x)) := by
  rw [edBi, Table.toBuiltins_of_lookup rfl, leaf1_apply]

theorem edBi_neg (x : α) :
    edBi mul add sub double neg d "neg" [enc x] = some (enc (neg x)) := by
  rw [edBi, Table.toBuiltins_of_lookup rfl, leaf1_apply]

theorem edBi_d : edBi mul add sub double neg d "d" [] = some (enc d) := by
  rw [edBi, Table.toBuiltins_of_lookup rfl, leaf0_apply]

end Leaves

variable [HaxEnc.Plain α]

/-! ## The pilot: extended-coordinates addition -/

/-- The addition of extended Edwards coordinates `(x, y, z, t)` over named field
    operations, in the formula and binding order of `Ristretto255.element_add`. -/
def edwardsAddLean (mul add sub : α → α → α) (double : α → α) (d : α)
    (p q : α × α × α × α) : α × α × α × α :=
  let dd := d
  let a := mul (sub p.2.1 p.1) (sub q.2.1 q.1)
  let b := mul (add p.2.1 p.1) (add q.2.1 q.1)
  let c := mul (mul p.2.2.2 (double dd)) q.2.2.2
  let dz := mul (double p.2.2.1) q.2.2.1
  let e := sub b a
  let f := sub dz c
  let g := add dz c
  let h := add b a
  (mul e f, mul g h, mul f g, mul e h)

/-- The literal of `edwardsAddLean` over the parameters `p`, `q`. -/
def edwardsAddImp : ImpExpr := reifyImp% 2 edwardsAddLean

/-- The literal of the pilot: the `let` chain of `Ristretto255.element_add_impExpr` in
    A-normal form, with the field accessors `.x`, `.y`, `.z`, `.t` read as the projections
    `0` to `3`, each operand of a call bound to a fresh name, and the constructor `RPoint`
    read as a tuple of variables. -/
theorem edwardsAddImp_eq : edwardsAddImp =
    .letBind "dd" (.app "d" [])
    (.letBind "p1" (.proj (.var "p") 1) (.letBind "p0" (.proj (.var "p") 0)
    (.letBind "t" (.app "sub" [.var "p1", .var "p0"])
    (.letBind "q1" (.proj (.var "q") 1) (.letBind "q0" (.proj (.var "q") 0)
    (.letBind "t_1" (.app "sub" [.var "q1", .var "q0"])
    (.letBind "a" (.app "mul" [.var "t", .var "t_1"])
    (.letBind "p1_1" (.proj (.var "p") 1) (.letBind "p0_1" (.proj (.var "p") 0)
    (.letBind "t_2" (.app "add" [.var "p1_1", .var "p0_1"])
    (.letBind "q1_1" (.proj (.var "q") 1) (.letBind "q0_1" (.proj (.var "q") 0)
    (.letBind "t_3" (.app "add" [.var "q1_1", .var "q0_1"])
    (.letBind "b" (.app "mul" [.var "t_2", .var "t_3"])
    (.letBind "p3" (.proj (.var "p") 3)
    (.letBind "t_4" (.app "double" [.var "dd"])
    (.letBind "t_5" (.app "mul" [.var "p3", .var "t_4"])
    (.letBind "q3" (.proj (.var "q") 3)
    (.letBind "c" (.app "mul" [.var "t_5", .var "q3"])
    (.letBind "p2" (.proj (.var "p") 2)
    (.letBind "t_6" (.app "double" [.var "p2"])
    (.letBind "q2" (.proj (.var "q") 2)
    (.letBind "dz" (.app "mul" [.var "t_6", .var "q2"])
    (.letBind "e" (.app "sub" [.var "b", .var "a"])
    (.letBind "f" (.app "sub" [.var "dz", .var "c"])
    (.letBind "g" (.app "add" [.var "dz", .var "c"])
    (.letBind "h" (.app "add" [.var "b", .var "a"])
    (.letBind "t_7" (.app "mul" [.var "e", .var "f"])
    (.letBind "t_8" (.app "mul" [.var "g", .var "h"])
    (.letBind "t_9" (.app "mul" [.var "f", .var "g"])
    (.letBind "t_10" (.app "mul" [.var "e", .var "h"])
    (.tuple [.var "t_7", .var "t_8", .var "t_9", .var "t_10"])))))))))))))))))))))))))))))))) :=
  rfl

/-- **The pilot is validated.** From the entry environment binding `p` and `q`, the literal
    `edwardsAddImp` returns the encoding of `edwardsAddLean` under the table `edBi`. -/
theorem edwardsAdd_fnCorres (mul add sub : α → α → α) (double neg : α → α) (d : α) :
    FnCorres (edBi mul add sub double neg d) edwardsAddImp
      (A := (α × α × α × α) × (α × α × α × α) × Unit)
      (fun a => bindParams [("p", enc a.1), ("q", enc a.2.1)]) (fun _ => True)
      (fun a => edwardsAddLean mul add sub double d a.1 a.2.1) := by
  ascend_reified (edwardsAddLean mul add sub double d)
    using [edBi_mul, edBi_add, edBi_sub, edBi_double, edBi_d]

/-- The Rust type token of an extended point: a tuple of four field elements. -/
def edPointTy : Crypto.Hax.ImpRust.Tok := "(Fe,Fe,Fe,Fe)"

/-- The literal of the pilot prints as the Rust function
    `pub fn edwards_add(p : (Fe,Fe,Fe,Fe), q : (Fe,Fe,Fe,Fe)) -> (Fe,Fe,Fe,Fe)`, which
    `Crypto.Hax.parse_ppImpRustFnRet` reads back to `edwardsAddImp`. -/
theorem edwardsAdd_prints :
    (Crypto.Hax.ppImpRustFnRet "edwards_add" [("p", edPointTy), ("q", edPointTy)] edPointTy
      (fun _ => none) edwardsAddImp).isSome = true := by
  decide +kernel

/-! ## A conditional -/

/-- The negation of `x` when `b`, and `x` otherwise. -/
def condNegLean (neg : α → α) (b : Bool) (x : α) : α :=
  let y := neg x
  if b then y else x

/-- The literal of `condNegLean` over the parameters `b`, `x`. -/
def condNegImp : ImpExpr := reifyImp% 2 condNegLean

theorem condNegImp_eq : condNegImp =
    .letBind "y" (.app "neg" [.var "x"]) (.ifThenElse (.var "b") (.var "y") (.var "x")) := rfl

/-- From the entry environment binding `b` and `x`, the literal `condNegImp` returns the
    encoding of `condNegLean` under the table `edBi`. -/
theorem condNeg_fnCorres (mul add sub : α → α → α) (double neg : α → α) (d : α) :
    FnCorres (edBi mul add sub double neg d) condNegImp (A := Bool × α × Unit)
      (fun a => bindParams [("b", enc a.1), ("x", enc a.2.1)]) (fun _ => True)
      (fun a => condNegLean neg a.1 a.2.1) := by
  ascend_reified (condNegLean neg) using [edBi_neg]

/-! ## Boolean connectives in a condition -/

/-- The builtin table of the `Int` comparison `lt` and the Boolean connectives `&&`, `||`,
    `Not`, at the call names the reifier emits. -/
noncomputable def cmpBi : Builtins :=
  Table.toBuiltins [("lt", leaf2 (Hax.lt : Int → Int → Bool)), ("&&", leaf2 Hax.band),
    ("||", leaf2 Hax.bor), ("Not", leaf1 Hax.bnot)]

theorem cmpBi_lt (x y : Int) : cmpBi "lt" [enc x, enc y] = some (enc (Hax.lt x y)) := by
  rw [cmpBi, Table.toBuiltins_of_lookup rfl, leaf2_apply]

theorem cmpBi_band (x y : Bool) : cmpBi "&&" [enc x, enc y] = some (enc (Hax.band x y)) := by
  rw [cmpBi, Table.toBuiltins_of_lookup rfl, leaf2_apply]

theorem cmpBi_bor (x y : Bool) : cmpBi "||" [enc x, enc y] = some (enc (Hax.bor x y)) := by
  rw [cmpBi, Table.toBuiltins_of_lookup rfl, leaf2_apply]

theorem cmpBi_not (x : Bool) : cmpBi "Not" [enc x] = some (enc (Hax.bnot x)) := by
  rw [cmpBi, Table.toBuiltins_of_lookup rfl, leaf1_apply]

/-- The indicator of `x < y` and `y < 10`, a conjunction of two Boolean comparisons. -/
def bandCondLean (x y : Int) : Int := if x < y && y < 10 then 1 else 0

/-- The literal of `bandCondLean` over the parameters `x`, `y`. -/
def bandCondImp : ImpExpr := reifyImp% 2 bandCondLean

/-- The literal of `bandCondLean`: the conjunction is the call `&&` on the two comparisons. -/
theorem bandCondImp_eq : bandCondImp =
    .letBind "t" (.app "lt" [.var "x", .var "y"])
    (.letBind "t_1" (.lit (.int 10))
    (.letBind "t_2" (.app "lt" [.var "y", .var "t_1"])
    (.letBind "t_3" (.app "&&" [.var "t", .var "t_2"])
    (.ifThenElse (.var "t_3") (.letBind "t_4" (.lit (.int 1)) (.var "t_4"))
      (.letBind "t_5" (.lit (.int 0)) (.var "t_5")))))) := rfl

/-- From the entry environment binding `x` and `y`, the literal `bandCondImp` returns the
    encoding of `bandCondLean` under the table `cmpBi`. -/
theorem bandCond_fnCorres :
    FnCorres cmpBi bandCondImp (A := Int × Int × Unit)
      (fun a => bindParams [("x", enc a.1), ("y", enc a.2.1)]) (fun _ => True)
      (fun a => bandCondLean a.1 a.2.1) := by
  ascend_reified bandCondLean using [cmpBi_lt, cmpBi_band]

/-- The indicator of `¬ x < y` or `y < 10`, a proposition read under `decide`. -/
def propCondLean (x y : Int) : Int := if decide (¬ x < y ∨ y < 10) then 1 else 0

/-- The literal of `propCondLean` over the parameters `x`, `y`. -/
def propCondImp : ImpExpr := reifyImp% 2 propCondLean

/-- The literal of `propCondLean`: `¬` and `∨` are the calls `Not` and `||`. -/
theorem propCondImp_eq : propCondImp =
    .letBind "t" (.app "lt" [.var "x", .var "y"])
    (.letBind "t_1" (.app "Not" [.var "t"])
    (.letBind "t_2" (.lit (.int 10))
    (.letBind "t_3" (.app "lt" [.var "y", .var "t_2"])
    (.letBind "t_4" (.app "||" [.var "t_1", .var "t_3"])
    (.ifThenElse (.var "t_4") (.letBind "t_5" (.lit (.int 1)) (.var "t_5"))
      (.letBind "t_6" (.lit (.int 0)) (.var "t_6"))))))) := rfl

/-- From the entry environment binding `x` and `y`, the literal `propCondImp` returns the
    encoding of `propCondLean` under the table `cmpBi`. -/
theorem propCond_fnCorres :
    FnCorres cmpBi propCondImp (A := Int × Int × Unit)
      (fun a => bindParams [("x", enc a.1), ("y", enc a.2.1)]) (fun _ => True)
      (fun a => propCondLean a.1 a.2.1) := by
  ascend_reified propCondLean using [cmpBi_lt, cmpBi_bor, cmpBi_not]

/-! ## A body reduced before it is read -/

/-- The left fold of `add` over a list from the accumulator `acc`, by structural recursion
    on the list. -/
def foldAddL (add : α → α → α) : List α → α → α
  | [], acc => acc
  | x :: xs, acc => foldAddL add xs (add acc x)

/-- The fold of `add` over the list literal `[x, y, z]` from `x`. -/
def sumThreeLean (add : α → α → α) (x y z : α) : α := foldAddL add [x, y, z] x

/-- The literal of `sumThreeLean` over `x`, `y`, `z`, with `foldAddL` unfolded on the list
    literal before the body is read. -/
def sumThreeImp : ImpExpr := reifyImp% 3 sumThreeLean unfolding [foldAddL]

/-- The literal of `sumThreeLean`: three calls of `add`, one per element of the list (a test
    of the reduction pre-pass). -/
theorem sumThreeImp_eq : sumThreeImp =
    .letBind "t" (.app "add" [.var "x", .var "x"])
    (.letBind "t_1" (.app "add" [.var "t", .var "y"])
    (.letBind "t_2" (.app "add" [.var "t_1", .var "z"]) (.var "t_2"))) := rfl

/-- From the entry environment binding `x`, `y`, `z`, the literal `sumThreeImp` returns the
    encoding of `sumThreeLean add` under the table `edBi`. -/
theorem sumThree_fnCorres (mul add sub : α → α → α) (double neg : α → α) (d : α) :
    FnCorres (edBi mul add sub double neg d) sumThreeImp (A := α × α × α × Unit)
      (fun a => bindParams [("x", enc a.1), ("y", enc a.2.1), ("z", enc a.2.2.1)])
      (fun _ => True) (fun a => sumThreeLean add a.1 a.2.1 a.2.2.1) := by
  ascend_reified (sumThreeLean add) using [edBi_add]

/-! ## Closed terms reduced to integer literals -/

/-- Three additions of constants given by closed terms: the position of `7` in a list
    literal cast to `Int`, and the integer differences `2 - 5` and `5 - 2` of
    `Int.subNatNat`. -/
def closedConstLean (add : Int → Int → Int) (x : Int) : Int :=
  add (add (add x ((List.idxOf 7 [2, 7, 5] : Nat) : Int)) (Int.subNatNat 2 5))
    (Int.subNatNat 5 2)

/-- The literal of `closedConstLean` over `x`, with the closed applications of `List.idxOf`
    and `Int.subNatNat` reduced before the body is read. -/
def closedConstImp : ImpExpr :=
  reifyImp% 1 closedConstLean reducing [List.idxOf, Int.subNatNat] within 100

/-- The literal of `closedConstLean`: the closed terms are the integer literals `1`, `-3`
    and `3` (a test of the reduction pre-pass and of the literal forms `Nat.cast`,
    `Int.negSucc` and `Int.ofNat`). -/
theorem closedConstImp_eq : closedConstImp =
    .letBind "t" (.lit (.int 1))
    (.letBind "t_1" (.app "add" [.var "x", .var "t"])
    (.letBind "t_2" (.lit (.int (-3)))
    (.letBind "t_3" (.app "add" [.var "t_1", .var "t_2"])
    (.letBind "t_4" (.lit (.int 3))
    (.letBind "t_5" (.app "add" [.var "t_3", .var "t_4"]) (.var "t_5")))))) := rfl

/-- From the entry environment binding `x`, the literal `closedConstImp` returns the
    encoding of `closedConstLean add` under the table `edBi`. -/
theorem closedConst_fnCorres (mul add sub : Int → Int → Int) (double neg : Int → Int)
    (d : Int) :
    FnCorres (edBi mul add sub double neg d) closedConstImp (A := Int × Unit)
      (fun a => bindParams [("x", enc a.1)]) (fun _ => True)
      (fun a => closedConstLean add a.1) := by
  ascend_reified (closedConstLean add) using [edBi_add]

/-! ## Matches over a closed code tree -/

/-- A code tree: an input node, a stuck node, a receive node with two continuations, a
    sequence and the end. -/
inductive PilotCode where
  | input (d : Nat) (k : PilotCode)
  | stuck (k : PilotCode)
  | recv (d : Nat) (k kf : PilotCode)
  | seq (k₁ k₂ : PilotCode)
  | halt

/-- The blocking nodes of a code tree in order, by structural recursion. -/
def PilotCode.blocks : PilotCode → List PilotCode
  | .input d k => .input d k :: k.blocks
  | .stuck k => .stuck k :: k.blocks
  | .recv d k kf => .recv d k kf :: (k.blocks ++ kf.blocks)
  | .seq k₁ k₂ => k₁.blocks ++ k₂.blocks
  | .halt => []

/-- One step on the block `b`: `x` added to `x` at an input node, to `neg x` at a stuck
    node, and to `add x x` at any other node (a match with a catch-all arm). -/
def pilotResume (add : α → α → α) (neg : α → α) (b : PilotCode) (x : α) : α :=
  add x (match b with
    | .input _ _ => x
    | .stuck _ => neg x
    | _ => add x x)

/-- The steps `pilotResume` on the blocks in order, by structural recursion on the list. -/
def pilotFold (add : α → α → α) (neg : α → α) : List PilotCode → α → α
  | [], x => x
  | b :: bs, x => pilotFold add neg bs (pilotResume add neg b x)

/-- A closed code tree computed by a fold: an input node at each even position below `3`
    and a stuck node at each odd one. -/
def pilotCode : PilotCode :=
  (List.range 3).foldr (fun i k => if i % 2 = 0 then .input i k else .stuck k) .halt

/-- The steps on the blocks of `pilotCode` from `x`. -/
def codeRunLean (add : α → α → α) (neg : α → α) (x : α) : α :=
  pilotFold add neg pilotCode.blocks x

/-- The literal of `codeRunLean` over `x`: the blocks of `pilotCode` reduced, the fold
    unfolded on them and each match reduced on its block. -/
def codeRunImp : ImpExpr :=
  reifyImp% 1 codeRunLean unfolding [pilotFold, pilotResume]
    reducing [pilotCode, PilotCode.blocks] within 1000

/-- From the entry environment binding `x`, the literal `codeRunImp` returns the encoding
    of `codeRunLean add neg` under the table `edBi`. -/
theorem codeRun_fnCorres (mul add sub : α → α → α) (double neg : α → α) (d : α) :
    FnCorres (edBi mul add sub double neg d) codeRunImp (A := α × Unit)
      (fun a => bindParams [("x", enc a.1)]) (fun _ => True)
      (fun a => codeRunLean add neg a.1) := by
  ascend_reified (codeRunLean add neg) using [edBi_add, edBi_neg]

/-! ## Arithmetic closed after a match is reduced -/

/-- A layout with one size field. -/
structure PilotLayout where
  /-- The size. -/
  k : Nat

/-- The layout of size `4`. -/
def pilotLayout : PilotLayout := ⟨4⟩

/-- One step on the block `b`: at an input node with datum `d`, `x` added to the integer
    `d + 4 + length of the blocks of the continuation`; at any other node, `x`. -/
def pilotOffset (add : Int → Int → Int) (b : PilotCode) (x : Int) : Int :=
  match b with
  | .input d k => add x (((d + pilotLayout.k + k.blocks.length : Nat) : Int))
  | _ => x

/-- The step `pilotOffset` on the input node with datum `3` whose continuation is a stuck
    node. -/
def offsetLean (add : Int → Int → Int) (x : Int) : Int :=
  pilotOffset add (.input 3 (.stuck .halt)) x

/-- The literal of `offsetLean` over `x`: the match reduced on the input node, after which
    the sum `3 + 4 + 1` and its cast to `Int` are closed and read as the literal `8`. -/
def offsetImp : ImpExpr :=
  reifyImp% 1 offsetLean unfolding [pilotOffset]
    reducing [pilotLayout, PilotLayout.k, PilotCode.blocks, List.length, HAdd.hAdd, instHAdd,
      Add.add, Nat.add, Nat.cast, instNatCastInt] within 100

/-- The literal of `offsetLean`: one addition of the integer literal `8`. -/
theorem offsetImp_eq : offsetImp =
    .letBind "t" (.lit (.int 8))
    (.letBind "t_1" (.app "add" [.var "x", .var "t"]) (.var "t_1")) := rfl

/-- From the entry environment binding `x`, the literal `offsetImp` returns the encoding of
    `offsetLean add` under the table `edBi`. -/
theorem offset_fnCorres (mul add sub : Int → Int → Int) (double neg : Int → Int) (d : Int) :
    FnCorres (edBi mul add sub double neg d) offsetImp (A := Int × Unit)
      (fun a => bindParams [("x", enc a.1)]) (fun _ => True)
      (fun a => offsetLean add a.1) := by
  ascend_reified (offsetLean add) using [edBi_add]

/-! ## The goal reduced as the literal was read -/

/-- A closed code tree computed by a fold over `40` positions: an input node at each
    multiple of `5`, a stuck node at each position `2` past one. -/
def pilotCodeL : PilotCode :=
  (List.range 40).foldr (fun i k => if i % 5 = 0 then .input i k else
    if i % 5 = 2 then .stuck k else k) .halt

/-- One step on the block `b`: `x` negated at an input node, unchanged at any other. -/
def pilotStepL (neg : α → α) (b : PilotCode) (x : α) : α :=
  match b with
  | .input _ _ => neg x
  | _ => x

/-- The steps `pilotStepL` on the blocks in order, by structural recursion on the list. -/
def pilotFoldL (neg : α → α) : List PilotCode → α → α
  | [], x => x
  | b :: bs, x => pilotFoldL neg bs (pilotStepL neg b x)

/-- The steps on the blocks of `pilotCodeL` from `x`. -/
def codeRunLLean (neg : α → α) (x : α) : α :=
  pilotFoldL neg pilotCodeL.blocks x

/-- The literal of `codeRunLLean` over `x`: the blocks of `pilotCodeL` reduced, the fold
    unfolded on them and each match reduced on its block. -/
def codeRunLImp : ImpExpr :=
  reifyImp% 1 codeRunLLean unfolding [pilotFoldL, pilotStepL]
    reducing [pilotCodeL, PilotCode.blocks] within 1000

/-- From the entry environment binding `x`, the literal `codeRunLImp` returns the encoding
    of `codeRunLLean neg`; the goal is compared over its function reduced by the clauses the
    literal was read with. -/
theorem codeRunL_fnCorres (mul add sub : α → α → α) (double neg : α → α) (d : α) :
    FnCorres (edBi mul add sub double neg d) codeRunLImp (A := α × Unit)
      (fun a => bindParams [("x", enc a.1)]) (fun _ => True)
      (fun a => codeRunLLean neg a.1) := by
  ascend_reified (codeRunLLean neg) using [edBi_neg]
    unfolding [pilotFoldL, pilotStepL] reducing [pilotCodeL, PilotCode.blocks] within 1000

end CatCrypt.Hax.ReifyImp

end
