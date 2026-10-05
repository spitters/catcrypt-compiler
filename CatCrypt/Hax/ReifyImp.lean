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
  `decide p`, `!`, `&&`, `||`) or an `Int` comparison (`<`, `≤`, `=`, read as the calls
  `lt`, `le`, `eq`);
* `some x` and `none`, read as the calls `Some` and `None` of the constructors of the
  hax value `.option`;
* `Int` and `Bool` literals.

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

* `reifyImp%` — the reifier
* `ascend_reified` — the validation tactic
* `edBi` — the builtin table of the field operations of the pilot
* `edwardsAddLean`, `edwardsAddImp` — the extended-coordinates addition of
  `Ristretto255.element_add` over named field operations, and its literal
* `condNegLean`, `condNegImp` — a conditional negation, and its literal

## Main results

* `edwardsAddImp_eq` — the literal of the pilot, stated in full
* `edwardsAdd_fnCorres` — the literal of the pilot denotes `edwardsAddLean`
* `edwardsAdd_prints` — the literal of the pilot prints as a Rust function
* `condNeg_fnCorres` — the literal of the conditional negation denotes `condNegLean`
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
    if e.isAppOfArity ``OfNat.ofNat 3 then
      if (← whnfR (e.getArg! 0)).isConstOf ``Int then
        if let some k := (e.getArg! 1).rawNatLit? then
          return ([], mkApp (mkConst ``Hax.ImpExpr.lit)
            (mkApp (mkConst ``Hax.ImpLit.int) (toExpr (Int.ofNat k))))
    if e.isAppOfArity ``not 1 then
      let (bs, as) ← reifyAtoms ctx [e.appArg!]
      return (bs, ← mkCall "not" as)
    if e.isAppOfArity ``and 2 then
      let (bs, as) ← reifyAtoms ctx [e.getArg! 0, e.getArg! 1]
      return (bs, ← mkCall "and" as)
    if e.isAppOfArity ``or 2 then
      let (bs, as) ← reifyAtoms ctx [e.getArg! 0, e.getArg! 1]
      return (bs, ← mkCall "or" as)
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
    return (bs, ← mkCall "not" [a])
  if p.isAppOfArity ``And 2 || p.isAppOfArity ``Or 2 then
    let (bs, a) ← atomize (← reifyCond ctx (p.getArg! 0))
    let (bs', b) ← atomize (← reifyCond ctx (p.getArg! 1))
    return (bs ++ bs', ← mkCall (if p.isAppOfArity ``And 2 then "and" else "or") [a, b])
  throwError "reifyImp: condition outside the fragment: {p}"

end

/-- The literal of the definition `c` over its last `n` explicit parameters, the binders
    before them read as operations. -/
def reifyConst (c : Name) (n : Nat) : MetaM Expr := do
  let info ← getConstInfo c
  let some v := info.value? | throwError "reifyImp: {c} has no body"
  lambdaTelescope v fun xs body => do
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
    their binder names. Without `n`, every explicit binder is a parameter. -/
elab "reifyImp% " n?:(num)? f:ident : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo f
  let n ← match n? with
    | some n => pure n.getNat
    | none => do
      let v := (← getConstInfo c).value?.getD (mkConst ``Unit)
      lambdaTelescope v fun xs _ => do
        let ys ← xs.filterM fun x => do
          let d ← x.fvarId!.getDecl
          return !d.binderInfo.isInstImplicit && !(← whnfR d.type).isSort
        return ys.size
  reifyConst c n

/-- `ascend_reified s using [l₁, …]` closes a goal `FnCorres bi e entry (fun _ => True) f`
    by the ascent generator on the literal `e`, the table `bi`, the leaf lemmas `lᵢ` and
    the surface function `s`, whose explicit binder names are the parameter names of the
    literal. The entry environment is `bindParams` of the parameter bindings; the goal is
    closed when the generated statement is definitionally the goal. -/
elab "ascend_reified " sur:term " using " "[" ls:ident,* "]" : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  unless goal.isAppOfArity ``Hax.Ascent.FnCorres 8 do
    throwError "ascend_reified: the goal is not a FnCorres statement"
  let bi := goal.getArg! 0
  let e ← whnf (goal.getArg! 4)
  let surface ← instantiateMVars (← Term.elabTermAndSynthesize sur none)
  let params ← forallTelescopeReducing (← inferType surface) fun xs _ => do
    let xs ← xs.filterM fun x => return !(← x.fvarId!.getBinderInfo).isInstImplicit
    xs.toList.mapM fun x => return nameStr (← x.fvarId!.getUserName)
  let lems ← ls.getElems.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
  let leaves ← Hax.Ascent.Gen.indexLeaves {} lems
  let spec : Hax.Ascent.Gen.FnSpec := {
    lit := e, surface, params, globals := [], bi, leaves, hints := {}
    entry := fun A Γ₀l => do
      let entry ← withLocalDeclD `a A fun a => do
        mkLambdaFVars #[a] (← mkAppM ``Hax.Ascent.bindParams #[Γ₀l.beta #[a]])
      let hentry ← withLocalDeclD `a A fun a => withLocalDeclD `h (mkConst ``True) fun h => do
        mkLambdaFVars #[a, h] (← mkAppM ``Hax.Ascent.binds_bindParams #[Γ₀l.beta #[a]])
      return (entry, hentry) }
  let res ← Hax.Ascent.Gen.ascendFn spec
  unless ← isDefEq res.thmTy goal do
    throwError "ascend_reified: the generated statement{indentExpr res.thmTy}\nis not the goal"
  closeMainGoal `ascend_reified res.thm

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

end CatCrypt.Hax.ReifyImp

end
