/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.GenRules
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
applies one rule of `HaxAscent/Ascent/GenRules.lean` or `HaxAscent/Ascent/AscendHax.lean`
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
* the termination of a `whileFold`, proved from a measure `(y - x).toNat`, or a sum of two,
  read off the comparisons of the loop (`proveTerm`); the decrease is proved with the
  subterms outside integer arithmetic, pairs and array lengths generalized (`termAtoms`).

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
step function. No loop specification is written by hand. A variable the body rebinds at
another type is left out of the invariant, and the loop is derived again without it.

A counted loop also carries an accumulator invariant `J` (`corresB_forFoldPJ`,
`corresB_forFoldGJ`), and a while loop likewise (`corresB_whileFoldGJ`): the candidate
facts of `accFactCands` that hold initially and that the step keeps. They state that the
arrays of non-integer elements in the accumulator, reached through `Prod` projections, are
nonempty, that the arrays inside their elements are nonempty (`AllP`), and, for an array
not built by a constructor, that this holds of the accumulator when it holds of the
initial value; in a while loop, that an integer component is not negative. The body runs
under `J` as part of its guard; a fact the step does not keep is left out and the loop is
derived again.

## Nonempty arrays and the guard

`index` on an array whose elements are not integers corresponds to `Hax.index` on a
nonempty array only (`RuntimeOps.index_pos`): on an empty array the runtime returns
`.int 0`, not the encoding of the default element. The hypothesis `0 < a.size` of the leaf
is proved from the guard at the call (`proveArr`): from a fact of the guard, from the
array's construction (`repeat`, `array_update`, `push`, a loop whose steps keep it), from
the element facts of an array of arrays (`AllNE`) and of the arrays inside the elements
(`AllP`, `of_index_allP`), from `is_empty` tests, by `omega` from loop bounds over
`Hax.array_len`, and from the body of a generated function whose result it is
(`unfoldGen?`). Struct projections, struct updates and field updates are read through
`projNorm`. An array argument of the function whose nonemptiness follows from none of
these is asked for as a guard fact of the function, under the hypothesis `0 < n` for an
integer argument `n` when the facts at the call imply it; the function is derived again
under that guard (`FnResult.guard`), and its call lemma takes the guard as a hypothesis,
which callers prove in the same way. Once a derivation has asked for a fact past its
guard, a leaf hypothesis it cannot prove is admitted while it collects the others, and
that derivation is discarded; the facts of a conjunction and the two facts an index reads
(`0 < a.size` and `AllP`) are asked for together (`both`), so that one derivation collects
the guard.
`vec_remove` takes an index in range, an integer comparison proved in the same way.

A `forFoldReturn` is a counted loop whose body exits by returning from the function
(`corresG_forFoldReturnG`); an `Option` match on a variable is a two-way branch on
`isSome` whose `Some` arm binds the payload (`corresG_optMatch`); a match with a single
arm whose pattern is a tuple of variables binds the components of the scrutinee
(`corresB_matchTuple`).

## Types

The type of a binding is the type of the leaf result that produces it. When a leaf is
polymorphic in its result (`new []`, `None`), a type hint decides it: the type of the
surface `let` of the same name (`GCtx.hints`), the hint of the enclosing expression for
the body of a `let` and the branches of a conditional or match, the return type of the
surface function for a `return` value and the whole body (`GCtx.retTy?`), and, for the
arguments of a call whose name has a single leaf lemma, the argument types of that lemma
(`leafArgHints`). Parameter types come from the surface signature, with a struct type in
its encoded form (`FnSpec.normTy`). A tuple whose last component has a product type types
that component as `Boxed`, so that the pair encodes as a pair; the argument encoding of a
struct of many fields is assembled from its components (`synthLarge`).

## The oracle

The generated function is compared with the printed surface function by definitional
equality at default transparency (`FnResult.oracle`).

## Main definitions

* `SVal`, `SEnv`, `StCtx`, `GCtx`, `GenM`, `GRes`, `GuardReq`
* `proveArr` — the nonemptiness facts of arrays; `projNorm`, `unfoldGen?`
* `accFactCands` — the candidate facts of a loop accumulator invariant
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

/-- An instance of `HaxArgs A`, `HaxEnc.Inj τ` or `HaxTupleEnc.Inj τ`, assembled from the
    instances of the components of a product when instance resolution alone exceeds its
    size bound (a struct of many fields). -/
partial def synthLarge (cls : Expr) : MetaM Expr := do
  let cls ← instantiateMVars cls
  if let some i ← (try synthInstance? cls catch _ => pure none) then return i
  let prodArgs (τ : Expr) : MetaM (Option (Expr × Expr)) := do
    match (← whnfR τ).getAppFnArgs with
    | (``Prod, #[α, β]) => return some (α, β)
    | _ => return none
  let inj (τ : Expr) : MetaM Expr := do
    synthLarge (← mkAppOptM ``Hax.Ascent.HaxEnc.Inj #[τ, none])
  let tinj (τ : Expr) : MetaM Expr := do
    synthLarge (← mkAppOptM ``Hax.Ascent.HaxTupleEnc.Inj #[τ, none])
  match cls.getAppFnArgs with
  | (``Hax.Ascent.HaxArgs, #[A]) =>
    let some (α, β) ← prodArgs A | throwError "failed to synthesize{indentExpr cls}"
    mkAppOptM ``Hax.Ascent.HaxArgs.prod
      #[α, β, none, ← inj α, ← synthLarge (← mkAppM ``Hax.Ascent.HaxArgs #[β])]
  | (``Hax.Ascent.HaxEnc.Inj, #[τ, _]) =>
    let some (α, β) ← prodArgs τ | throwError "failed to synthesize{indentExpr cls}"
    mkAppOptM ``Hax.Ascent.HaxEnc.Inj.prod #[α, β, none, ← inj α, none, ← tinj β]
  | (``Hax.Ascent.HaxTupleEnc.Inj, #[τ, _]) =>
    match ← prodArgs τ with
    | some (α, β) =>
      mkAppOptM ``Hax.Ascent.HaxTupleEnc.Inj.prod #[α, β, none, ← inj α, none, ← tinj β]
    | none => mkAppOptM ``Hax.Ascent.HaxTupleEnc.Inj.single #[τ, none, ← inj τ]
  | _ => throwError "failed to synthesize{indentExpr cls}"

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

/-! ### Nonempty arrays -/

/-- A request for guard facts: the argument tuple variable of the function and the facts
    about it the derivation asks for. -/
structure GuardReq where
  /-- The argument tuple variable. -/
  top : Expr
  /-- The facts asked for, as propositions over `top`. -/
  need : IO.Ref (Array Expr)
  /-- The integer arguments: a fact is asked for under the hypothesis that one of them is
      positive when the facts at the request imply it. -/
  ints : Array Expr := #[]
  /-- The number of facts of the guard the current derivation runs under: the facts past
      it were asked for by this derivation, which is derived again. -/
  base : Option (IO.Ref Nat) := none

/-- The conjunction of the propositions, `True` for none. -/
def andList : List Expr → Expr
  | [] => mkConst ``True
  | [p] => p
  | p :: ps => mkApp2 (mkConst ``_root_.And) p (andList ps)

/-- The proposition is a conjunction of array facts: `0 < a.size`, `AllNE a`, `AllP P a`,
    `0 ≤ x` for an integer `x`, or `True`, each possibly under hypotheses. -/
partial def isArrFact (p : Expr) : MetaM Bool := do
  let p := (← instantiateMVars p).headBeta
  if let .forallE _ _ b _ := p then
    return !b.hasLooseBVars && (← isArrFact b)
  match p.getAppFnArgs with
  | (``_root_.And, #[a, b]) => return (← isArrFact a) && (← isArrFact b)
  | (``True, _) => return true
  | (``Hax.Ascent.AllNE, _) => return true
  | (``Hax.Ascent.AllP, _) => return true
  | (``LT.lt, #[ty, _, _, s]) => return ty.isConstOf ``Nat && s.isAppOfArity ``Array.size 2
  -- the sign fact of an integer accumulator of a while loop
  | (``LE.le, #[ty, _, z, _]) => return ty.isConstOf ``Int && z == toExpr (0 : Int)
  | _ => return false

/-- The proofs of the conjuncts of the hypothesis `h`. -/
partial def splitFacts (h : Expr) : MetaM (Array Expr) := do
  let ty ← whnfR (← instantiateMVars (← inferType h))
  if ty.isAppOfArity ``_root_.And 2 then
    return (← splitFacts (← mkAppM ``_root_.And.left #[h])) ++
      (← splitFacts (← mkAppM ``_root_.And.right #[h]))
  if ty.isConstOf ``True then return #[]
  return #[h]

/-- The proofs of the conjuncts of the propositional hypotheses among `xs`. -/
def factsOf (xs : Array Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  for x in xs do
    if ← isProp (← inferType x) then out := out ++ (← splitFacts x)
  return out

/-- The proposition `0 < a.size`. -/
def neProp (a : Expr) : MetaM Expr := do
  mkAppM ``LT.lt #[mkNatLit 0, ← mkAppM ``Array.size #[a]]

/-- The proposition `AllNE a`. -/
def allProp (a : Expr) : MetaM Expr := mkAppM ``Hax.Ascent.AllNE #[a]

/-- The closed subterms of `e` (without loose bound variables) satisfying `p`, added to
    `acc`, each shared subterm visited once. -/
def subtermsWhere (p : Expr → Bool) (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let r ← IO.mkRef acc
  e.forEachWhere (fun x => p x && !x.hasLooseBVars) fun x => r.modify (·.push x)
  r.get

/-- The term with every projection of a pair reduced: `(a, b).1` becomes `a`. -/
def reduceProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    let comp (i : Nat) (y : Expr) : TransformStep :=
      if y.isAppOfArity ``Prod.mk 4 then .visit y.getAppArgs[2 + i]! else .continue
    match x with
    | .proj ``Prod i y => return comp i y
    | _ =>
      match x.getAppFnArgs with
      | (``Prod.fst, #[_, _, y]) => return comp 0 y
      | (``Prod.snd, #[_, _, y]) => return comp 1 y
      | _ => return .continue)

/-- The equations `Hax.add a b = a + b`, `Hax.sub a b = a - b` and `Hax.mul a b = a * b` of
    the integer operations of the runtime in the terms, which `omega` reads. -/
def arithOpEqs (es : Array Expr) : MetaM (Array Expr) := do
  let isOp (x : Expr) : Bool :=
    (x.isAppOfArity ``Hax.add 4 || x.isAppOfArity ``Hax.sub 4 || x.isAppOfArity ``Hax.mul 4) &&
      x.getAppArgs[0]!.isConstOf ``Int
  let mut xs := #[]
  for e in es do
    xs ← subtermsWhere isOp (← instantiateMVars e) xs
  let mut out := #[]
  for x in xs do
    let args := x.getAppArgs
    let op := if x.isAppOf ``Hax.add then ``HAdd.hAdd
      else if x.isAppOf ``Hax.sub then ``HSub.hSub else ``HMul.hMul
    let rhs ← mkAppM op #[args[2]!, args[3]!]
    out := out.push (← mkExpectedTypeHint (← mkEqRefl x) (← mkEq x rhs))
  return out

/-- The length equations of the arrays in the terms, which `omega` reads: for each subterm
    `Hax.array_len b` the equation `Hax.array_len b = b.size` (`array_len_eq`), and for `b`
    built by the runtime the length of `b` in terms of the length of the array it is built
    from (`array_len_array_update`, `array_len_push`, `array_len_vec_remove`), followed through
    nested constructions. -/
def arrayLenEqs (es : Array Expr) : MetaM (Array Expr) := do
  let mut todo := #[]
  for e in es do
    todo ← subtermsWhere (·.isAppOfArity ``Hax.array_len 2) (← instantiateMVars e) todo
  let mut seen : Array Expr := #[]
  let mut out := #[]
  while h : 0 < todo.size do
    let x := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.push x
    let b := x.getAppArgs[1]!
    out := out.push (← mkAppM ``Hax.Ascent.array_len_eq #[b])
    -- the array `b` is built from an array by the runtime: its length equation
    let built? : Option (Name × Array Expr) :=
      if b.isAppOfArity ``Hax.array_update 4 then
        some (``Hax.Ascent.array_len_array_update, b.getAppArgs[1:4].toArray)
      else if b.isAppOfArity ``Hax.push 3 then
        some (``Hax.Ascent.array_len_push, b.getAppArgs[1:3].toArray)
      else
        let r? := match b with
          | .proj ``Prod 1 r => some r
          | _ => if b.isAppOfArity ``Prod.snd 3 then some b.getAppArgs[2]! else none
        match r? with
        | some r =>
          if r.isAppOfArity ``Hax.vec_remove 4 then
            some (``Hax.Ascent.array_len_vec_remove, #[r.getAppArgs[2]!, r.getAppArgs[3]!])
          else none
        | none => none
    let some (lem, args) := built? | continue
    let s ← saveState
    try
      let pf ← mkAppM lem args
      let some (_, _, rhs) := (← inferType pf).eq? | s.restore; continue
      -- stated at the subterm itself, so that `omega` reads one atom for it
      out := out.push (← mkExpectedTypeHint pf (← mkEq x rhs))
      todo ← subtermsWhere (·.isAppOfArity ``Hax.array_len 2) rhs todo
    catch _ => s.restore
  return out

/-- The subterms `min x y` of `e`, added to `acc`. -/
def minsOf (e : Expr) (acc : Array Expr) : MetaM (Array Expr) :=
  subtermsWhere (·.isAppOfArity ``Min.min 4) e acc

/-- The facts, with each fact `Hax.band a b = true` or `Hax.bor a b = false` followed by the
    facts about its operands. -/
partial def splitBoolFacts (facts : Array Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  for f in facts do
    out := out.push f
    let fty ← instantiateMVars (← inferType f)
    let some (_, lhs, rhs) := fty.eq? | continue
    let lems := if rhs.isConstOf ``Bool.true && lhs.isAppOfArity ``Hax.band 2 then
        [``Hax.Ascent.band_true_left, ``Hax.Ascent.band_true_right]
      else if rhs.isConstOf ``Bool.false && lhs.isAppOfArity ``Hax.bor 2 then
        [``Hax.Ascent.bor_false_left, ``Hax.Ascent.bor_false_right]
      else []
    for lem in lems do
      out := out ++ (← splitBoolFacts #[← mkAppM lem #[f]])
  return out

/-- The arithmetic facts that follow from the facts: the integer comparisons of the
    runtime read as propositions, including the operands of `Hax.band` and `Hax.bor`
    (`splitBoolFacts`), and the bounds of the minima the facts mention. -/
def arithFacts (facts : Array Expr) : MetaM (Array Expr) := do
  let facts ← splitBoolFacts facts
  -- the lemmas by the comparison at the head of the fact and its value
  let lemsOf (c : Name) (v : Bool) : List Name :=
    match c, v with
    | ``Hax.beq, true => [``Hax.Ascent.beq_true_int]
    | ``Hax.beq, false => [``Hax.Ascent.beq_false_int]
    | ``Hax.bne, true => [``Hax.Ascent.bne_true_int]
    | ``Hax.bne, false => [``Hax.Ascent.bne_false_int]
    | ``Hax.lt, true => [``Hax.Ascent.lt_true_int]
    | ``Hax.lt, false => [``Hax.Ascent.lt_false_int]
    | ``Hax.le, true => [``Hax.Ascent.le_true_int]
    | ``Hax.le, false => [``Hax.Ascent.le_false_int]
    | ``Hax.gt, true => [``Hax.Ascent.gt_true_int]
    | ``Hax.gt, false => [``Hax.Ascent.gt_false_int]
    | ``Hax.ge, true => [``Hax.Ascent.ge_true_int]
    | ``Hax.ge, false => [``Hax.Ascent.ge_false_int]
    | _, _ => []
  let mut out := #[]
  let mut mins := #[]
  for f in facts do
    let fty ← instantiateMVars (← inferType f)
    mins ← minsOf fty mins
    let some (_, lhs, rhs) := fty.eq? | continue
    unless rhs.isConstOf ``Bool.true || rhs.isConstOf ``Bool.false do continue
    let some c := lhs.getAppFn.constName? | continue
    for lem in lemsOf c (rhs.isConstOf ``Bool.true) do
      let s ← saveState
      try
        -- at instance transparency: a comparison of another type fails without unfolding
        -- its operands
        out := out.push (← withTransparency .instances (mkAppM lem #[f]))
        break
      catch _ => s.restore
  for m in mins do
    let args := m.getAppArgs
    unless args[0]!.isConstOf ``Int do continue
    out := out.push (← mkAppM ``Int.min_le_left #[args[2]!, args[3]!])
    out := out.push (← mkAppM ``Int.min_le_right #[args[2]!, args[3]!])
  return out

/-- A proof of an arithmetic proposition: by evaluation, from a fact, or by `omega` over
    the facts, their arithmetic consequences and the local context. -/
def proveArith (p : Expr) (facts : Array Expr) : MetaM Expr := do
  -- evaluation decides closed propositions only
  unless (← instantiateMVars p).hasFVar do
    if let some pf ← boundedTry? (proveDecide p) then return pf
  for f in facts do
    if ← isDefEqBounded (← inferType f) p then return f
  -- `omega` reads the goal and the facts with the projections of pairs reduced, so that a
  -- state variable read through the state tuple is the variable
  let p₀ := p
  let p ← reduceProjs (← instantiateMVars p)
  let facts ← facts.mapM fun f => do
    let t ← instantiateMVars (← inferType f)
    let t' ← reduceProjs t
    if t' == t then pure f else mkExpectedTypeHint f t'
  let g ← mkFreshExprMVar p
  let some g' ← g.mvarId!.falseOrByContra | throwError "side: cannot prove{indentExpr p}"
  let hyps ← g'.withContext getLocalHyps
  let extra ← arithFacts facts
  let tys := #[p] ++ (← (facts ++ extra).mapM inferType)
  let ops ← arithOpEqs tys
  let lens ← arrayLenEqs tys
  try
    Lean.Elab.Tactic.Omega.omega
      (hyps.toList ++ facts.toList ++ extra.toList ++ ops.toList ++ lens.toList) g'
  catch _ => throwError "side: cannot prove{indentExpr p}"
  mkExpectedTypeHint (← instantiateMVars g) p₀

/-- The array and the reading of the argument that reaches it through `Prod.fst` and
    `Prod.snd`. -/
partial def pathBase (e : Expr) : MetaM (Expr × (Expr → MetaM Expr)) := do
  if let .mdata _ x := e then return ← pathBase x
  if let .proj ``Prod i x := e then
    let (b, k) ← pathBase x
    return (b, fun z => do mkAppM (if i == 0 then ``Prod.fst else ``Prod.snd) #[← k z])
  match e.getAppFnArgs with
  | (``Prod.fst, #[_, _, x]) =>
    let (b, k) ← pathBase x
    return (b, fun z => do mkAppM ``Prod.fst #[← k z])
  | (``Prod.snd, #[_, _, x]) =>
    let (b, k) ← pathBase x
    return (b, fun z => do mkAppM ``Prod.snd #[← k z])
  | _ => return (e, pure)

/-- The arrays `x` of the subterms `Hax.array_len x` of `e`, added to `acc`. -/
def lensOf (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let ls ← subtermsWhere (·.isAppOfArity ``Hax.array_len 2) e #[]
  return acc ++ ls.map (·.appArg!)

/-- The constant is a definition whose body, under its parameters, is a path of
    `Prod.fst` and `Prod.snd` from its last parameter: a struct projection of an
    extraction. -/
def isProjDef (c : Name) : MetaM Bool := do
  let some (.defnInfo d) := (← getEnv).find? c | return false
  lambdaTelescope d.value fun xs b => do
    let some x := xs.back? | return false
    let mut e := b
    for _ in [0:64] do
      match e with
      | .mdata _ y => e := y
      | .proj ``Prod _ y => e := y
      | _ =>
        match e.getAppFnArgs with
        | (``Prod.fst, #[_, _, y]) | (``Prod.snd, #[_, _, y]) => e := y
        | _ => break
    return e == x

/-- The term with its struct projections and struct updates unfolded and the projections
    of pairs reduced: `«.f» (struct_update_fst s v)` becomes `v`. A constant under a
    projection is unfolded when its value is a pair. -/
partial def projNorm (e : Expr) : MetaM Expr := do
  let e ← whnfR (← instantiateMVars e)
  let step (i : Nat) (mk : Expr → Expr) (x : Expr) : MetaM Expr := do
    let x' ← projNorm x
    let comp (p : Expr) : Option Expr :=
      if p.isAppOfArity ``Prod.mk 4 then some p.getAppArgs[2 + i]! else none
    if let some c := comp x' then return ← projNorm c
    -- a constant is unfolded, a few times, while its value is not a pair
    let mut y := x'
    for _ in [0:4] do
      unless y.getAppFn.isConst && !(y.getAppFn.constName!.getRoot == `Hax) do break
      let some y₁ ← unfoldDefinition? y | break
      y ← whnfR y₁
      if let some c := comp y then return ← projNorm c
    return mk x'
  match e with
  | .proj ``Prod i x => return ← step i (fun x' => .proj ``Prod i x') x
  | _ => pure ()
  match e.getAppFnArgs with
  | (``Prod.fst, #[α, β, x]) => step 0 (fun x' => mkApp3 e.getAppFn α β x') x
  | (``Prod.snd, #[α, β, x]) => step 1 (fun x' => mkApp3 e.getAppFn α β x') x
  | (``Hax.struct_update_fst, _) | (``Hax.struct_update_snd, _) =>
    match ← unfoldDefinition? e with
    | some e' => projNorm e'
    | none => return e
  | (`Hax.Ascent.fieldSet, _) | (`Hax.Ascent.fieldGet, _) =>
    -- the field instances unfold to pairs and projections
    let e' ← withTransparency .default (whnf e)
    if e' == e then return e else projNorm e'
  | (c, _) =>
    if !c.isAnonymous && (← isProjDef c) then
      if let some e' ← unfoldDefinition? e then return ← projNorm e'
    return e

/-- An array fact with its arrays in `projNorm` form: `0 < a.size`, `AllNE a` and
    `AllP P a`; another proposition is returned unchanged. -/
def arrFactNorm (p : Expr) : MetaM Expr := do
  let p := (← instantiateMVars p).headBeta
  match p.getAppFnArgs with
  | (``LT.lt, #[ty, inst, z, s]) =>
    if ty.isConstOf ``Nat && s.isAppOfArity ``Array.size 2 then
      let s' := mkApp2 s.appFn!.appFn! s.appFn!.appArg! (← projNorm s.appArg!)
      return mkApp4 p.getAppFn ty inst z s'
    return p
  | (``Hax.Ascent.AllNE, #[β, a]) => return mkApp2 p.getAppFn β (← projNorm a)
  | (``Hax.Ascent.AllP, #[α, P, a]) => return mkApp3 p.getAppFn α P (← projNorm a)
  | _ => return p

/-- A proof of `goal` from one fact: the fact itself, or a fact `H → goal` whose
    hypothesis `H` follows from the facts: an array fact through `arr?`, otherwise an
    arithmetic fact. Array facts are compared in `arrFactNorm` form at reducible
    transparency. -/
def matchFact (goal : Expr) (facts : Array Expr)
    (arr? : Option (Expr → Array Expr → MetaM Expr) := none) : MetaM (Option Expr) := do
  let arrGoal ← isArrFact goal
  let goalN ← if arrGoal then arrFactNorm goal else pure goal
  let same (p : Expr) : MetaM Bool := do
    if arrGoal && (← isArrFact p) then withReducible (isDefEq (← arrFactNorm p) goalN)
    else isDefEqBounded p goal
  for f in facts do
    let fty := (← instantiateMVars (← inferType f)).headBeta
    if ← same fty then return some f
    if let .forallE _ h q _ := fty then
      unless q.hasLooseBVars do
        if ← same q then
          let s ← saveState
          try
            -- an array hypothesis is proved from the other facts
            if let some arr := arr? then
              if ← isArrFact h then
                return some (mkApp f (← arr h (facts.filter (· != f))))
            return some (mkApp f (← proveArith h facts))
          catch _ => s.restore
  return none

/-- A proof of `goal` that is one of the facts, or a conjunction of facts. -/
partial def ofFacts (goal : Expr) (facts : Array Expr) : MetaM (Option Expr) := do
  let goal := (← instantiateMVars goal).headBeta
  if let (``_root_.And, #[a, b]) := goal.getAppFnArgs then
    let some pa ← ofFacts a facts | return none
    let some pb ← ofFacts b facts | return none
    return some (mkApp4 (mkConst ``_root_.And.intro) a b pa pb)
  matchFact goal facts

/-- The array paths of a type through `Prod`: each path, as a list of `Prod.snd` (`true`)
    and `Prod.fst` (`false`) steps, with the array type it reaches. -/
partial def arrPaths (ty : Expr) (depth : Nat := 8) : MetaM (List (List Bool × Expr)) := do
  let ty ← whnfR ty
  if ty.isAppOfArity ``Array 1 then return [([], ty)]
  if depth == 0 then return []
  if let (``Prod, #[α, β]) := ty.getAppFnArgs then
    let l ← arrPaths α (depth - 1)
    let r ← arrPaths β (depth - 1)
    return l.map (fun (p, t) => (false :: p, t)) ++ r.map (fun (p, t) => (true :: p, t))
  return []

/-- The path applied to a term. -/
def applyPath (x : Expr) (p : List Bool) : MetaM Expr :=
  p.foldlM (fun e b => mkAppM (if b then ``Prod.snd else ``Prod.fst) #[e]) x

/-- A term `p (Hax.index a i)` for a path `p` of `Prod.fst` and `Prod.snd`: the path, read
    from the element outwards, the array and the index. -/
partial def pathOverIndex (t : Expr) : Option (List Bool × Expr × Expr) :=
  match t with
  | .mdata _ x => pathOverIndex x
  | .proj ``Prod i x => (pathOverIndex x).map fun (p, a, j) => (p ++ [i == 1], a, j)
  | _ =>
    match t.getAppFnArgs with
    | (``Prod.fst, #[_, _, x]) => (pathOverIndex x).map fun (p, a, j) => (p ++ [false], a, j)
    | (``Prod.snd, #[_, _, x]) => (pathOverIndex x).map fun (p, a, j) => (p ++ [true], a, j)
    | (``Hax.index, #[_, _, a, i]) => some ([], a, i)
    | _ => none

/-- The call `f.gen x` or `f.merged x` of a generated function unfolded to the generated
    body at `x`. -/
def unfoldGen? (t : Expr) : MetaM (Option Expr) := do
  let some (.str _ s) := t.getAppFn.constName? | return none
  unless s == "gen" || s == "merged" do return none
  let some t' ← unfoldDefinition? t | return none
  return some (← projNorm t'.headBeta)

/-- The array is the value of an array constructor. -/
def isArrCtor (t : Expr) : Bool :=
  [``Hax.push, ``Hax.repeat_, ``Hax.from_elem, ``Hax.array_update, ``List.toArray,
    ``Array.empty, ``Hax.with_capacity, ``Array.emptyWithCapacity].any t.isAppOf

/-- The results of `x` and `y`. Under a guard request, `y` is attempted also when `x`
    fails, and the failure of `x` is raised afterwards: the guard facts that both ask for are
    requested in one derivation. -/
def both {α β : Type} (req? : Option GuardReq) (x : MetaM α) (y : MetaM β) :
    MetaM (α × β) := do
  if req?.isNone then return (← x, ← y)
  let s ← saveState
  try
    let a ← x
    return (a, ← y)
  catch ex =>
    s.restore
    try discard y catch _ => pure ()
    s.restore
    throw ex

mutual

/-- A proof of a conjunction of array facts from the facts `facts`. An array whose
    nonemptiness follows from no rule and whose free variables are only the argument tuple
    of the function is asked for as a guard fact through `req?`. -/
partial def proveArr (req? : Option GuardReq) (goal : Expr) (facts : Array Expr) :
    MetaM Expr := do
  let goal := (← instantiateMVars goal).headBeta
  if goal.isForall then
    return ← forallTelescope goal fun xs body => do
      mkLambdaFVars xs (← proveArr req? body (facts ++ (← factsOf xs)))
  match goal.getAppFnArgs with
  | (``_root_.And, #[a, b]) =>
    let (pa, pb) ← both req? (proveArr req? a facts) (proveArr req? b facts)
    return mkApp4 (mkConst ``_root_.And.intro) a b pa pb
  | (``True, _) => return mkConst ``True.intro
  | _ => pure ()
  if let some pf ← matchFact goal facts (some (proveArr req?)) then return pf
  match goal.getAppFnArgs with
  | (``LT.lt, #[ty, _, _, s]) =>
    if ty.isConstOf ``Nat && s.isAppOfArity ``Array.size 2 then
      return ← mkExpectedTypeHint (← proveNE req? s.appArg! facts) goal
    proveArith goal facts
  | (``Hax.Ascent.AllNE, #[_, t]) =>
    mkExpectedTypeHint (← proveAll req? t facts) goal
  | (``Hax.Ascent.AllP, #[_, P, t]) =>
    mkExpectedTypeHint (← proveAllP req? P t facts) goal
  | _ => proveArith goal facts

/-- A proof of `P (p (Hax.index a i))` for the path `p` from `0 < a.size` and
    `AllP (fun x => P (p x)) a` (`of_index_allP`). -/
partial def proveOverIndex (req? : Option GuardReq) (P : Expr → MetaM Expr) (p : List Bool)
    (a i : Expr) (facts : Array Expr) : MetaM Expr := do
  let elemTy ← inferType (← mkAppM ``Hax.index #[a, i])
  let Q ← withLocalDeclD `x elemTy fun x => do mkLambdaFVars #[x] (← P (← applyPath x p))
  let allQ ← mkAppM ``Hax.Ascent.AllP #[Q, a]
  let (h, ha) ← both req? (do proveArr req? (← neProp a) facts) (proveArr req? allQ facts)
  let pf ← mkAppOptM ``Hax.Ascent.of_index_allP #[none, none, Q, a, h, ha, i]
  mkExpectedTypeHint pf (← P (← applyPath (← mkAppM ``Hax.index #[a, i]) p))

/-- A proof of `0 < t.size`. -/
partial def proveNE (req? : Option GuardReq) (t : Expr) (facts : Array Expr) : MetaM Expr := do
  let t ← projNorm t
  -- a component of an element: from the elements of the array
  if let some (p@(_ :: _), a, i) := pathOverIndex t then
    let s ← saveState
    try return ← proveOverIndex req? neProp p a i facts
    catch _ => s.restore
  match t.getAppFnArgs with
  | (``Hax.array_update, #[_, a, i, v]) =>
    mkAppM ``Hax.Ascent.ne_array_update #[i, v, ← proveArr req? (← neProp a) facts]
  | (``Hax.push, #[_, a, v]) => mkAppM ``Hax.Ascent.ne_push #[a, v]
  | (``Hax.repeat_, #[_, v, n]) =>
    mkAppM ``Hax.Ascent.ne_repeat #[v, ← proveArith (← mkAppM ``LT.lt #[toExpr (0 : Int), n]) facts]
  | (``Hax.from_elem, #[_, v, n]) =>
    mkAppM ``Hax.Ascent.ne_from_elem #[v, ← proveArith (← mkAppM ``LT.lt #[toExpr (0 : Int), n]) facts]
  | (``Hax.deref, #[_, x]) => proveArr req? (← neProp x) facts
  | (``Hax.to_vec, #[_, x]) => proveArr req? (← neProp x) facts
  | (``Hax.index, #[_, _, a, i]) =>
    let (h, ha) ← both req? (do proveArr req? (← neProp a) facts)
      (do proveArr req? (← allProp a) facts)
    mkAppM ``Hax.Ascent.ne_index #[h, ha, i]
  | _ =>
    if let some pf ← neOfFacts t facts then return pf
    -- the result of a generated function: from its definition
    if let some t' ← unfoldGen? t then
      let s ← saveState
      try return ← mkExpectedTypeHint (← proveNE req? t' facts) (← neProp t)
      catch _ => s.restore
    provePres req? t neProp facts

/-- A proof of `0 < t.size` from a fact that `t` is not empty, or by `omega` from facts
    about `Hax.array_len t` (a loop over the indices of `t`). -/
partial def neOfFacts (t : Expr) (facts : Array Expr) : MetaM (Option Expr) := do
  let goal ← neProp t
  for f in facts do
    let fty ← instantiateMVars (← inferType f)
    unless (fty.find? (·.isConstOf ``Hax.is_empty)).isSome do continue
    for lem in [``Hax.Ascent.ne_of_not_is_empty, ``Hax.Ascent.ne_of_is_empty_false] do
      let s ← saveState
      try
        let pf ← mkAppM lem #[f]
        if ← isDefEq (← inferType pf) goal then return some pf
        s.restore
      catch _ => s.restore
  let mut lens : Array Expr := #[]
  for f in facts do
    lens ← lensOf (← instantiateMVars (← inferType f)) lens
  for x in lens do
    unless ← withReducible (isDefEq (← projNorm x) (← projNorm t)) do continue
    let s ← saveState
    try
      let pf ← proveArith (← neProp x) (facts.push (← mkAppM ``Hax.Ascent.array_len_eq #[x]))
      return some (← mkExpectedTypeHint pf goal)
    catch _ => s.restore
  return none

/-- A proof of `AllNE t`. -/
partial def proveAll (req? : Option GuardReq) (t : Expr) (facts : Array Expr) :
    MetaM Expr := do
  let t ← projNorm t
  match t.getAppFnArgs with
  | (``Hax.array_update, #[_, a, i, v]) =>
    mkAppM ``Hax.Ascent.allNE_array_update
      #[i, ← proveArr req? (← allProp a) facts, ← proveArr req? (← neProp v) facts]
  | (``Hax.push, #[_, a, v]) =>
    mkAppM ``Hax.Ascent.allNE_push
      #[← proveArr req? (← allProp a) facts, ← proveArr req? (← neProp v) facts]
  | (``Hax.repeat_, #[_, v, n]) =>
    mkAppM ``Hax.Ascent.allNE_repeat #[n, ← proveArr req? (← neProp v) facts]
  | (``Hax.from_elem, #[_, v, n]) =>
    mkAppM ``Hax.Ascent.allNE_from_elem #[n, ← proveArr req? (← neProp v) facts]
  | (``Hax.deref, #[_, x]) => proveArr req? (← allProp x) facts
  | (``Hax.to_vec, #[_, x]) => proveArr req? (← allProp x) facts
  | _ =>
    -- through a loop the nonemptiness of the array is carried with that of its elements
    let pf ← provePres req? t
      (fun z => do return mkApp2 (mkConst ``_root_.And) (← neProp z) (← allProp z)) facts
    mkAppM ``_root_.And.right #[pf]

/-- A proof of `AllP P t`: from the construction of `t`, from the elements of an array of
    which `t` is a component of an element, or through `provePres`. -/
partial def proveAllP (req? : Option GuardReq) (P t : Expr) (facts : Array Expr) :
    MetaM Expr := do
  let t ← projNorm t
  let allP (x : Expr) : MetaM Expr := mkAppM ``Hax.Ascent.AllP #[P, x]
  let atP (v : Expr) : Expr := (mkApp P v).headBeta
  if let some (p, a, i) := pathOverIndex t then
    let s ← saveState
    try return ← proveOverIndex req? allP p a i facts
    catch _ => s.restore
  match t.getAppFnArgs with
  | (``Hax.array_update, #[_, a, i, v]) =>
    mkAppOptM ``Hax.Ascent.allP_array_update
      #[none, P, a, i, v, ← proveArr req? (← allP a) facts, ← proveArr req? (atP v) facts]
  | (``Hax.push, #[_, a, v]) =>
    mkAppOptM ``Hax.Ascent.allP_push
      #[none, P, a, v, ← proveArr req? (← allP a) facts, ← proveArr req? (atP v) facts]
  | (``Hax.repeat_, #[_, v, n]) =>
    mkAppOptM ``Hax.Ascent.allP_repeat #[none, P, v, n, ← proveArr req? (atP v) facts]
  | (``Hax.from_elem, #[_, v, n]) =>
    mkAppOptM ``Hax.Ascent.allP_from_elem #[none, P, v, n, ← proveArr req? (atP v) facts]
  | (``Hax.deref, #[_, x]) => proveArr req? (← allP x) facts
  | (``Hax.to_vec, #[_, x]) => proveArr req? (← allP x) facts
  | _ =>
    if let some t' ← unfoldGen? t then
      let s ← saveState
      try return ← mkExpectedTypeHint (← proveAllP req? P t' facts) (← allP t)
      catch _ => s.restore
    provePres req? t allP facts

/-- A proof of `mkP t` where `t` reads a conditional or the result of a loop through
    `Prod.fst` and `Prod.snd`: the predicate of both branches, or of the initial value and
    every step. Otherwise `t` is asked for as a guard fact through `req?`. -/
partial def provePres (req? : Option GuardReq) (t : Expr) (mkP : Expr → MetaM Expr)
    (facts : Array Expr) : MetaM Expr := do
  let goal ← mkP t
  if let some pf ← ofFacts goal facts then return pf
  let (b, k) ← pathBase t
  let b ← whnfR b
  let bTy ← inferType b
  let P ← withLocalDeclD `z bTy fun z => do mkLambdaFVars #[z] (← mkP (← k z))
  let apply (lem : Name) : MetaM Expr := do
    let c ← mkConstWithFreshMVarLevels lem
    let lty ← inferType c
    let (mvs, bis, concl) ← forallMetaTelescope lty
    let some iP := (binderNamesOf lty).findIdx? (· == `P) | throwError "side: {lem}"
    unless ← isDefEq mvs[iP]! P do throwError "side: {lem} does not apply"
    unless ← isDefEq concl (P.beta #[b]) do throwError "side: {lem} does not apply"
    for m in mvs, bi in bis do
      let m' ← instantiateMVars m
      unless m'.isMVar do continue
      if bi.isInstImplicit then
        let inst ← synthInstance (← instantiateMVars (← inferType m'))
        unless ← isDefEq m' inst do throwError "side: {lem} instance"
        continue
      let ty ← instantiateMVars (← inferType m')
      unless ← isProp ty do continue
      let pf ← forallTelescope ty fun xs body => do
        let fs := facts ++ (← factsOf xs)
        mkLambdaFVars xs (← proveArr req? body fs)
      unless ← isDefEq m' pf do throwError "side: {lem}"
    let e ← instantiateMVars (mkAppN c mvs)
    if e.hasExprMVar then throwError "side: {lem} open"
    return e
  let lemErrs ← IO.mkRef (#[] : Array MessageData)
  let tryLems (lems : List Name) : MetaM (Option Expr) := do
    for lem in lems do
      let s ← saveState
      try return some (← apply lem)
      catch ex =>
        s.restore
        lemErrs.modify (·.push m!"{lem}: {ex.toMessageData}")
    return none
  let lems := match b.getAppFn.constName? with
    | some ``Hax.foldRange => [``Hax.Ascent.foldRange_pres, ``Hax.Ascent.foldRange_pres_lt]
    | some ``Hax.foldRangeRev => [``Hax.Ascent.foldRangeRev_pres]
    | some ``Hax.Ascent.cfState => [``Hax.Ascent.forFold_stepCF_pres]
    | some ``ite => [``Hax.Ascent.prop_ite]
    | _ => []
  if let some pf ← tryLems lems then
    return ← mkExpectedTypeHint pf goal
  if let some req := req? then
    let goal ← instantiateMVars goal
    unless goal.hasMVar do
      if (collectFVars {} goal).fvarIds.all (· == req.top.fvarId!) then
        -- under the hypothesis that an integer argument is positive, when the facts here
        -- imply it (the array is read only when a count argument is positive)
        let mut fact := goal
        for p in req.ints do
          let s ← saveState
          let pos ← mkAppM ``LT.lt #[toExpr (0 : Int), p]
          try
            discard <| proveArith pos facts
            fact ← mkArrow pos goal
            break
          catch _ => s.restore
        let need ← req.need.get
        unless ← need.anyM (fun n => isDefEq n fact) do req.need.set (need.push fact)
        throwError "guard: {fact}"
  throwError "side: cannot prove{indentExpr goal}\n{← lemErrs.get}"

end

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

/-- The branch of the conditional binding list `l` (an `ite` whose arguments are `args`)
    that a hypothesis selects: a proof that the list is that branch, and the branch. The
    selection does not depend on the variable looked up, so it is made once per list and
    kept in `sel`. A hypothesis is tried only when its right side is the Boolean its lemma
    asks for, and a selection is kept only when the lemma's conditional is the list at
    reducible transparency. -/
def selectBranch (l : Expr) (args : Array Expr) (hyps : Array Expr)
    (sel : IO.Ref (Array (Expr × Option (Expr × Expr)))) : MetaM (Option (Expr × Expr)) := do
  if let some (_, r) := (← sel.get).find? (·.1 == l) then return r
  let mut res := none
  for h in hyps do
    let some (_, _, rhs) := (← instantiateMVars (← inferType h)).eq? | continue
    let rhs ← whnfR rhs
    for (lem, bi, exit) in [(``Hax.Ascent.ite_of_left_exit, 4, true),
        (``Hax.Ascent.ite_of_right_exit, 3, true), (``Hax.Ascent.ite_of_left_noexit, 4, false),
        (``Hax.Ascent.ite_of_right_noexit, 3, false)] do
      unless rhs.isConstOf (if exit then ``Bool.false else ``Bool.true) do continue
      let s ← saveState
      try
        let eqPf ← mkAppM lem #[args[3]!, args[4]!, h]
        let some (_, lhs, _) := (← inferType eqPf).eq? | throwError "no"
        unless ← withReducible (isDefEq lhs l) do throwError "no"
        res := some (eqPf, args[bi]!)
        break
      catch _ => s.restore
    if res.isSome then break
  sel.modify (·.push (l, res))
  return res

/-- A proof of `bindLookup l x = some v`. `sel` keeps the branch selections of the
    conditional lists met (`selectBranch`). -/
partial def proveLookup (l : Expr) (x : String) (v : Expr) (hyps : Array Expr)
    (sel? : Option (IO.Ref (Array (Expr × Option (Expr × Expr)))) := none) : MetaM Expr := do
  let sel ← match sel? with
    | some r => pure r
    | none => IO.mkRef #[]
  let l' ← whnfR (← instantiateMVars l)
  if l'.isAppOfArity ``ite 5 then
    let args := l'.getAppArgs
    let some b := args[1]!.eq?.map (·.2.1) | throwError "side: condition of{shortExpr l'}"
    -- a hypothesis that selects one branch
    if let some (eqPf, sub) ← selectBranch l' args hyps sel then
      let s ← saveState
      try
        let pf ← proveLookup sub x v hyps sel
        return ← mkEqNDRec' eqPf pf x
      catch _ => s.restore
    let some v1 ← lookupExpr args[3]! x | throwError "side: {x} unbound in a branch"
    let some v2 ← lookupExpr args[4]! x | throwError "side: {x} unbound in a branch"
    let h1 ← proveLookup args[3]! x v1 hyps sel
    let h2 ← proveLookup args[4]! x v2 hyps sel
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

/-- A proof of `BindsSub l m` for an explicit list `m`. The branch selections of the
    conditional lists in `l` are shared by the entries of `m`. -/
partial def proveBindsSub (l m : Expr) (hyps : Array Expr)
    (sel? : Option (IO.Ref (Array (Expr × Option (Expr × Expr)))) := none) : MetaM Expr := do
  let sel ← match sel? with
    | some r => pure r
    | none => IO.mkRef #[]
  let m' ← whnfR (← instantiateMVars m)
  match m'.getAppFnArgs with
  | (``List.nil, _) => mkAppM ``Hax.Ascent.bindsSub_nil_intro #[l]
  | (``List.cons, #[_, h, t]) =>
    let h ← whnfR h
    let (``Prod.mk, #[_, _, k, v]) := h.getAppFnArgs | throwError "side: binding{shortExpr h}"
    let some x := strOf? (← instantiateMVars k) | throwError "side: binding name{shortExpr k}"
    let pl ← proveLookup l x v hyps sel
    let ps ← proveBindsSub l t hyps sel
    mkAppM ``Hax.Ascent.bindsSub_cons_intro #[pl, ps]
  | _ => throwError "side: binding list{shortExpr m'}"

/-- A proof of a side condition, with the hypotheses of its telescope. -/
partial def closeProp (p : Expr) (hyps : Array Expr) : MetaM Expr := do
  let p := (← instantiateMVars p).headBeta
  if !p.isConstOf ``True && (← isArrFact p) then
    return ← mkExpectedTypeHint (← proveArr none p (← factsOf hyps)) p
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
        let inst ← try synthInstance (← inferType m') catch ex =>
          throwError "{ex.toMessageData} (in {r.rule})"
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
  /-- The return type of the surface function, the type hint of a `return` value. -/
  retTy? : Option Expr := none
  /-- The request for guard facts about the arguments. -/
  req? : Option GuardReq := none

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

/-- A hypothesis of a leaf that the caller proves under the guard: a conjunction of array
    facts, or an integer comparison (`vec_remove` in range). -/
def isPendFact (p : Expr) : MetaM Bool := do
  if ← isArrFact p then return true
  let p := (← instantiateMVars p).headBeta
  match p.getAppFnArgs with
  | (``LT.lt, #[ty, _, _, _]) | (``LE.le, #[ty, _, _, _]) => return ty.isConstOf ``Int
  | _ => return false

/-- Match the call `f vs` against the leaf lemmas of `f`. With `strict`, a leaf whose
    result type differs from the type hint is skipped. With `pend`, a hypothesis of the
    leaf that is a conjunction of array facts or an integer comparison and is not decided
    is left as a metavariable of the proof, for the caller to prove under the guard. -/
def matchLeaf (f : String) (vs : Array SVal) (hint? : Option Expr) (strict : Bool)
    (pend : Bool := false) (errs? : Option (IO.Ref (Array String)) := none) :
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
      -- the instances whose class the arguments determine
      for m in mvs, b in bis do
        if b.isInstImplicit then
          let m' ← instantiateMVars m
          if m'.isMVar then
            let cls ← instantiateMVars (← inferType m')
            unless cls.hasExprMVar do
              if let some inst ← (synthInstance? cls : MetaM _) then
                discard <| isDefEq m' inst
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
              try m'.mvarId!.assign (← proveDecide mty)
              catch ex =>
                unless pend && (← isPendFact mty) do throw ex
      let pf ← instantiateMVars (mkAppN c mvs)
      if pf.hasExprMVar then
        unless pend do throwError "open"
        for m in (← getMVars pf) do
          unless ← isPendFact (← instantiateMVars (← m.getType)) do throwError "open"
      return some (pf, ← instSVal sv)
    catch ex =>
      if let some r := errs? then
        let m ← ex.toMessageData.toString
        r.modify (·.push s!"{lem.components.getLast!}: {m}")
      (s.restore : MetaM Unit)
  return none

/-- Match a call to a tagged runtime name `op#w` on integer arguments with the width
    family lemmas `RuntimeOps.tagged1` and `RuntimeOps.tagged2`; the tag `size` is the
    width `Hax.usizeBits`. -/
def matchTagged (f : String) (vs : Array SVal) : GenM (Option (Expr × SVal)) := do
  let [op, wS] := f.splitOn "#" | return none
  let some w := (if wS == "size" then some (mkConst ``Hax.usizeBits) else
    wS.toNat?.map mkNatLit) | return none
  let some tms := vs.toList.mapM (·.tm?) | return none
  for (lem, n) in [(``Hax.Ascent.RuntimeOps.tagged1, 1), (``Hax.Ascent.RuntimeOps.tagged2, 2)] do
    unless tms.length == n do continue
    let s ← (Meta.saveState : MetaM Meta.SavedState)
    try
      for v in vs do
        unless ← isDefEq (v.ty?.getD boolTy) intTy do throwError "no"
      let r ← rapp lem
      r.set `f (mkStrLit f); r.set `op (mkStrLit op); r.set `w w
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

/-- The argument types of a call `f` with `n` arguments when `f` has a single leaf lemma:
    the type `τ` of each argument of its left side that is an encoding `enc (x : τ)` with
    `τ` closed. They are the type hints of the arguments. -/
def leafArgHints (f : String) (n : Nat) : GenM (List (Option Expr)) := do
  let some #[lem] := (← read).leaves[f]? | return []
  let s ← (Meta.saveState : MetaM Meta.SavedState)
  try
    let c ← mkConstWithFreshMVarLevels lem
    let (_, _, concl) ← forallMetaTelescope (← inferType c)
    let some (_, lhs, _) := concl.eq? | throwError "no"
    let some args ← listElems? lhs.appArg! | throwError "no"
    unless args.length == n do throwError "no"
    let tys ← args.mapM fun a => do
      match (← instantiateMVars a).getAppFnArgs with
      | (``Hax.Ascent.HaxEnc.enc, #[ty, _, _]) =>
        let ty ← instantiateMVars ty
        return if ty.hasExprMVar then none else some ty
      | _ => return none
    s.restore
    return tys
  catch _ =>
    s.restore
    return []

/-! ### Syntactic scans -/

/-- The elements of a list literal built from `List.cons` and `List.nil`. -/
partial def consElems (e : Expr) : List Expr :=
  match e.getAppFnArgs with
  | (``List.cons, #[_, h, t]) => h :: consElems t
  | _ => []

/-- The variables a match pattern binds. -/
partial def patVars (p : Expr) : List String :=
  match p.getAppFnArgs with
  | (``Hax.ImpPat.varPat, #[n]) => (strOf? n).toList
  | (``Hax.ImpPat.somePat, #[q]) => patVars q
  | (``Hax.ImpPat.okPat, #[q]) => patVars q
  | (``Hax.ImpPat.errPat, #[q]) => patVars q
  | (``Hax.ImpPat.tuplePat, #[qs]) => (consElems qs).flatMap patVars
  | _ => []

/-- The names bound by `letBind`, `assign` or a match pattern in an expression, closures
    excluded. -/
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
          let xty ← inferType x
          if xty.isConstOf ``Hax.ImpExpr then boundNames x
          -- a match arm: the variables of its pattern and the names its body binds
          else if xty.isAppOfArity ``Prod 2 && xty.appArg!.isConstOf ``Hax.ImpExpr then
            let (``Prod.mk, #[_, _, p, b]) := (← whnfR x).getAppFnArgs | pure []
            pure (patVars p ++ (← boundNames b))
          else pure []
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

/-- The candidate facts of a loop accumulator invariant `J`: for each accumulator
    component `j` named `k`, the key of the fact and the fact as a predicate of the
    component. `Gσ0` is the guard before the loop and `vs` the initial values.

    * `ne[]` and `all`: an array component is nonempty, and its elements are nonempty;
    * `ne p`, `all p q`: the arrays of non-integer elements reached from the component by a
      path `p` of `Prod` projections are nonempty, and the arrays reached from their
      elements by a path `q` are nonempty (`AllP`);
    * `cne p`, `call p q`: the same facts under the hypothesis that they hold of the
      initial value, where they do not hold initially and the initial array is not built
      by a constructor;
    * `nn` (with `ints`): an integer component is not negative.

    A fact other than a conditional one is kept when it holds initially; the caller
    checks that the body keeps each fact. -/
def accFactCands (Gσ0 : Expr) (M : List (String × SVal)) (tys : List Expr)
    (jdrop : List (String × String)) (ints : Bool := false) :
    MetaM (List (Nat × String × String × Expr)) := do
  let holds (p : Expr) : MetaM Bool := withLocalDeclD `hG Gσ0 fun hG => do
    let s ← (Meta.saveState : MetaM Meta.SavedState)
    try
      discard <| proveArr none p (← splitFacts hG)
      pure true
    catch _ =>
      (s.restore : MetaM Unit)
      pure false
  let mut jc : List (Nat × String × String × Expr) := []
  for (k, v) in M, t in tys, j in [0:M.length] do
    let some v0 := v.tm? | continue
    let pred (f : Expr → MetaM Expr) : MetaM Expr :=
      withLocalDeclD `z t fun z => do mkLambdaFVars #[z] (← f z)
    let mut cands : List (String × Expr) := []
    let tw ← whnfR t
    if ints && tw.isConstOf ``Int then
      cands := cands ++ [("nn", ← pred fun z => mkAppM ``LE.le #[toExpr (0 : Int), z])]
    if tw.isAppOfArity ``Array 1 then
      cands := cands ++ [("ne[]", ← pred neProp)]
      if (← whnfR tw.appArg!).isAppOfArity ``Array 1 then
        cands := cands ++ [("all", ← pred allProp)]
    for (p, arrTy) in (← arrPaths t).take 12 do
      let elemTy ← whnfR arrTy.appArg!
      if elemTy.isConstOf ``Int then continue
      let ctor := isArrCtor (← projNorm (← applyPath v0 p))
      let neP (x : Expr) : MetaM Expr := do neProp (← applyPath x p)
      unless p.isEmpty do cands := cands ++ [(s!"ne{p}", ← pred neP)]
      unless ctor do
        cands := cands ++ [(s!"cne{p}", ← pred fun x => do mkArrow (← neP v0) (← neP x))]
      for (q, qTy) in (← arrPaths elemTy 4).take 4 do
        if (← whnfR qTy.appArg!).isConstOf ``Int then continue
        let Q ← withLocalDeclD `y elemTy fun y => do
          mkLambdaFVars #[y] (← neProp (← applyPath y q))
        let allP (x : Expr) : MetaM Expr := do
          mkAppM ``Hax.Ascent.AllP #[Q, ← applyPath x p]
        cands := cands ++ [(s!"all{p}{q}", ← pred allP)]
        unless ctor do
          cands := cands ++
            [(s!"call{p}{q}", ← pred fun x => do mkArrow (← allP v0) (← allP x))]
    for (key, P) in cands do
      if jdrop.contains (k, key) then continue
      if key.startsWith "c" then
        unless jc.any (fun (j', _, key', _) => j' == j && "c" ++ key' == key) do
          jc := jc ++ [(j, k, key, P)]
      else if ← holds (P.beta #[v0]) then jc := jc ++ [(j, k, key, P)]
  return jc

def isTrueE (e : Expr) : MetaM Bool := return (← instantiateMVars e).isConstOf ``Bool.true
def isFalseE (e : Expr) : MetaM Bool := return (← instantiateMVars e).isConstOf ``Bool.false

/-! ### Termination of while loops -/

/-- The heads the termination tactic of a while loop reads: pairs, conditionals, the
    propositional and Boolean connectives, integer arithmetic and comparisons, and the
    runtime operations it unfolds or has a length lemma for (`array_len_vec_remove`,
    `array_len_array_update`, `array_len_push`). -/
def termHeads : List Name :=
  [`Prod.mk, `Prod.fst, `Prod.snd, `ite, `dite, `Eq, `Ne, `Not, `And, `Or, `Iff, `True,
   `False, `LT.lt, `LE.le, `GT.gt, `GE.ge, `HAdd.hAdd, `HSub.hSub, `HMul.hMul, `HDiv.hDiv,
   `HMod.hMod, `Neg.neg, `OfNat.ofNat, `Int.toNat, `Int.ofNat, `Nat.cast, `NatCast.natCast,
   `decide, `Bool.true, `Bool.false, `and, `or, `not, `Bool.and, `Bool.or, `Bool.not,
   `BEq.beq, `bne, ``Unit.unit, ``PUnit.unit, ``ControlFlow.Continue, ``ControlFlow.Break,
   ``Hax.Ascent.stepCF, ``Array.size, ``Hax.add, ``Hax.sub, ``Hax.mul, ``Hax.div, ``Hax.rem,
   ``Hax.Div, ``Hax.Rem, ``Hax.lt, ``Hax.le, ``Hax.gt,
   ``Hax.ge, ``Hax.beq, ``Hax.bne, ``Hax.band, ``Hax.bor, ``Hax.bnot, ``Hax.Not,
   ``Hax.array_len, ``Hax.array_update, ``Hax.vec_remove, ``Hax.push]

/-- Whether `e` is data: neither a proof, nor a type, nor an instance of a class. -/
def isDataTerm (e : Expr) : MetaM Bool := do
  if ← isProof e then return false
  if ← isType e then return false
  return (← isClass? (← inferType e)).isNone

/-- The heads that `projNorm` reduces: pair projections, struct updates, field access and
    the struct projections of an extraction. -/
def projHead (c : Name) : MetaM Bool := do
  if [``Prod.fst, ``Prod.snd, ``Hax.struct_update_fst, ``Hax.struct_update_snd,
      `Hax.Ascent.fieldSet, `Hax.Ascent.fieldGet].contains c then return true
  isProjDef c

/-- The term with `projNorm` applied at every projection, struct update and field access
    outside the atoms of `termAtoms`, whose arguments are left as they are. -/
def termNorm (e : Expr) : MetaM Expr :=
  Meta.transform e
    (pre := fun x => do
      match x.getAppFn with
      | .const c _ =>
        if termHeads.contains c || (← projHead c) then return .continue
        -- an atom is left as it is; an instance or a type is normalized with the terms
        -- it mentions
        if ← isDataTerm x then return .done x
        return .continue
      | _ => return .continue)
    (post := fun x => do
      let isProj ← match x, x.getAppFn with
        | .app .., .const c _ => projHead c
        | .proj .., _ => pure true
        | _, _ => pure false
      unless isProj do return .done x
      let x' ← projApp (← projNorm x)
      return if x' == x then .done x else .visit x')
where
  /-- The projections of pairs as applications of `Prod.fst` and `Prod.snd`: one form,
      which the arithmetic reads as one atom. -/
  projApp (e : Expr) : MetaM Expr :=
    Meta.transform e (post := fun y => do
      if let .proj ``Prod i z := y then
        return .done (← mkAppM (if i == 0 then ``Prod.fst else ``Prod.snd) #[z])
      return .done y)

/-- The atoms of a termination goal: the maximal subterms, without loose bound variables,
    that apply a constant outside `termHeads` and are data. -/
partial def termAtoms (e : Expr) : StateT (Array Expr) MetaM Unit := do
  match e with
  | .mdata _ b => termAtoms b
  | .proj _ _ b => termAtoms b
  | .lam _ d b _ | .forallE _ d b _ => do termAtoms d; termAtoms b
  | .letE _ _ v b _ => do termAtoms v; termAtoms b
  | .app .. | .const .. =>
    let f := e.getAppFn
    if let .const c _ := f then
      if !termHeads.contains c && !e.hasLooseBVars then
        if ← isDataTerm e then
          unless (← get).contains e do modify (·.push e)
          return
    else termAtoms f
    for a in e.getAppArgs do termAtoms a
  | _ => pure ()

/-- The path of pair projections from `x` to `e`, outermost component first; `true` is
    `Prod.snd`. -/
partial def pairPath? (x e : Expr) : Option (List Bool) :=
  if e == x then some [] else
  match e.getAppFnArgs with
  | (``Prod.fst, #[_, _, e']) => (pairPath? x e').map (· ++ [false])
  | (``Prod.snd, #[_, _, e']) => (pairPath? x e').map (· ++ [true])
  | _ => none

/-- The paths of the components of `x` that `e` reads: the maximal pair projections of
    `x` in `e`, and the empty path when `e` reads `x` itself. -/
partial def readPaths (x e : Expr) : List (List Bool) :=
  match pairPath? x e with
  | some p => [p]
  | none => match e with
    | .app f a => readPaths x f ++ readPaths x a
    | .lam _ d b _ | .forallE _ d b _ => readPaths x d ++ readPaths x b
    | .letE _ t v b _ => readPaths x t ++ readPaths x v ++ readPaths x b
    | .mdata _ b | .proj _ _ b => readPaths x b
    | _ => []

/-- The components of the tuple `g`, at the path `p` of a state, that no path of `reads`
    reaches: the largest subtuples outside every read component. -/
partial def unreadComps (reads : List (List Bool)) (p : List Bool) (g : Expr) : List Expr :=
  if reads.any (·.isPrefixOf p) then []
  else if !(reads.any (p.isPrefixOf ·)) then [g]
  else if g.isAppOfArity ``Prod.mk 4 then
    unreadComps reads (p ++ [false]) g.appFn!.appArg! ++
      unreadComps reads (p ++ [true]) g.appArg!
  else []

/-- Run `x` within a twentieth of the heartbeat budget, counted from its start: the error
    message when `x` throws or exceeds that budget, with the state restored. -/
def boundedTryT {α : Type} (x : TermElabM α) : TermElabM (Except String α) := do
  let s ← Term.saveState
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context
      (fun c => { c with maxHeartbeats := c.maxHeartbeats / 20 }) <| .ok <$> x)
    fun ex => do
      let m ← msgStr ex
      s.restore
      return .error (m.replace "\n" " ")

/-- The tactic that proves the decrease of a measure over one step of a while loop. -/
def termTactic : TermElabM Syntax := do
  `(tactic|
    (intros; rename_i hc hf; rw [Hax.Ascent.stepCF_eq_continue] at hf
     obtain ⟨hcb, heq⟩ := hf
     subst heq
     (repeat' split) <;>
       simp_all [Hax.add, Hax.sub, Hax.mul, Hax.div, Hax.rem, Hax.Div, Hax.Rem, Hax.lt, Hax.le, Hax.gt, Hax.ge, Hax.bne, Hax.beq,
         Hax.band, Hax.bor, Hax.bnot, Hax.Not, Hax.Ascent.array_len_array_update,
         Hax.Ascent.array_len_vec_remove, Hax.Ascent.array_len_push] <;>
       (repeat' split) <;> omega))

/-- A proof that the measure `μ` decreases over each step of the loop with condition `c`
    and step `f`, `∀ a a', c a = true → f a = .Continue a' → μ a' < μ a`. The statement is
    put in `termNorm` form, its atoms (`termAtoms`) are generalized, and `termTactic`
    proves the generalized statement. For a step `stepCF Cb w gb g`, the break values `w`
    and `gb` and the components of `g` outside the components `μ` reads (`readPaths`,
    `unreadComps`) are generalized as well. -/
def termDecrease (α c f μ : Expr) : TermElabM Expr := do
  withLocalDeclD `a α fun a => withLocalDeclD `a' α fun a' => do
    let hc ← mkEq (c.beta #[a]) (mkConst ``Bool.true)
    let cfTy ← whnf (← inferType (mkApp f a))
    let β := cfTy.getArg! 0
    let hf ← mkEq (f.beta #[a]) (← mkAppOptM ``ControlFlow.Continue #[β, α, a'])
    let concl ← mkAppM ``LT.lt #[μ.beta #[a'], μ.beta #[a]]
    let P ← mkArrow hc (← mkArrow hf concl)
    let hfN ← termNorm hf
    let conclN ← termNorm concl
    let Pn ← mkArrow (← termNorm hc) (← mkArrow hfN conclN)
    let ((), atoms) ← (termAtoms Pn).run #[]
    -- a step `stepCF Cb w gb g`: the break values `w`, `gb` and the components of the
    -- continue value `g` that the measure does not read are atoms as well
    let mut atoms := atoms
    if let some (_, lhs, _) := hfN.eq? then
      if lhs.isAppOf ``Hax.Ascent.stepCF && lhs.getAppNumArgs ≥ 4 then
        let args := lhs.getAppArgs
        let n := args.size
        let reads := readPaths a' conclN
        for t in [args[n - 3]!, args[n - 2]!] ++ unreadComps reads [] args[n - 1]! do
          if !t.hasLooseBVars && !atoms.contains t && (← isDataTerm t) then
            atoms := atoms.push t
    let decls : Array (Name × (Array Expr → TermElabM Expr)) ←
      atoms.mapIdxM fun i t => do
        return (Name.mkSimple s!"t{i}", fun _ => inferType t)
    withLocalDeclsD decls fun bs => do
      let Pa := Pn.replace fun t => (atoms.idxOf? t).map fun i => bs[i]!
      let H ← mkForallFVars (#[a, a'] ++ bs) Pa
      Meta.check H
      let mv ← mkFreshExprMVar H
      Term.withoutErrToSorry <| Term.runTactic mv.mvarId! (← termTactic) .term
      let log ← Core.getMessageLog
      if log.hasErrors then
        let errs := log.toList.filter (·.severity == .error)
        let m ← match errs with
          | e :: _ => e.data.toString
          | [] => pure ""
        throwError "tactic: {m}"
      let pf ← instantiateMVars mv
      let hdecTy ← mkForallFVars #[a, a'] P
      mkExpectedTypeHint (← mkLambdaFVars #[a, a'] (mkAppN pf (#[a, a'] ++ atoms))) hdecTy

mutual

/-- The derivation of `e` from the bindings `Γ` under the guard `G`. -/
partial def gen (Γ : SEnv) (G e : Expr) (hint? : Option Expr := none) : GenM GRes := do
  let e ← instantiateMVars e
  let (fn, args) := e.getAppFnArgs
  let r ← match fn, args with
    | ``Hax.ImpExpr.lit, #[l] => genLit Γ G e l
    | ``Hax.ImpExpr.unitVal, #[] => genUnit Γ G e
    | ``Hax.ImpExpr.var, #[x] => genVar Γ G e x
    | ``Hax.ImpExpr.letBind, #[x, v, b] => genSeqLike Γ G e (some x) v b hint?
    | ``Hax.ImpExpr.seq, #[a, b] => genSeqLike Γ G e none a b hint?
    | ``Hax.ImpExpr.ifThenElse, #[c, t, f] => genIte Γ G e c t f hint?
    | ``Hax.ImpExpr.app, #[f, as] => genApp Γ G e f as hint?
    | ``Hax.ImpExpr.tuple, #[es] => genTuple Γ G e es
    | ``Hax.ImpExpr.proj, #[a, i] => genProj Γ G e a i
    | ``Hax.ImpExpr.typeAscription, #[a, ty] => genPass Γ G ``Hax.Ascent.corresB_typeAscription a (some ty) hint?
    | ``Hax.ImpExpr.borrow, #[a] => genPass Γ G ``Hax.Ascent.corresB_borrow a none hint?
    | ``Hax.ImpExpr.deref, #[a] => genPass Γ G ``Hax.Ascent.corresB_deref a none hint?
    | ``Hax.ImpExpr.cfBreak, #[a] => genBreak Γ G e a
    | ``Hax.ImpExpr.forFold, #[var, lo, hi, body] => genForFold Γ G e var lo hi body
    | ``Hax.ImpExpr.forFoldRev, #[var, lo, hi, body] => genForFold Γ G e var lo hi body true
    | ``Hax.ImpExpr.forFoldReturn, #[var, lo, hi, body] => genForFoldReturn Γ G e var lo hi body
    | ``Hax.ImpExpr.match_, #[s, arms] => genMatch Γ G e s arms hint?
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
partial def genSeqLike (Γ : SEnv) (G _e : Expr) (x? : Option Expr) (v b : Expr)
    (bodyHint? : Option Expr := none) : GenM GRes := do
  let xs? := x?.bind fun x => strOf? x
  let hints := (← read).hints
  let hint? := xs?.bind fun x => hints[x]?
  let r1 ← gen Γ G v hint?
  let bodyEnv (N : SEnv) : SEnv := match xs? with
    | some x => (x, r1.val) :: N
    | none => N
  match r1.exit with
  | none =>
    let rb ← gen (bodyEnv r1.N) G b bodyHint?
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
    let rb ← gen (bodyEnv r1.N) Gb b bodyHint?
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

partial def genIte (Γ : SEnv) (G _e c t f : Expr) (hint? : Option Expr := none) :
    GenM GRes := do
  let rc ← gen Γ G c
  if rc.exit.isSome then throwError "construct: exit in a condition"
  let some B := rc.val.tm? | throwError "type: condition"
  unless ← isDefEq (rc.val.ty?.getD intTy) boolTy do throwError "type: condition"
  let Gt ← abstE (andE (← atState G) (← mkEq B trueE))
  let Gf ← abstE (andE (← atState G) (← mkEq B falseE))
  let rt ← gen rc.N Gt t hint?
  let rf ← gen rc.N Gf f hint?
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
  let (pt, Ct, Wt, Tt) ← liftG rt
  let (pf, Cf, Wf, Tf) ← liftG rf
  let r ← rapp ``Hax.Ascent.corresG_ifThenElse
  r.set `c c; r.set `t t; r.set `e f; r.set `B (← abstE B)
  r.set `Ct (← abstE Ct); r.set `Ce (← abstE Cf)
  r.set `hc rc.proof; r.set `ht pt; r.set `he pf
  iteTail B (← r.done) rt rf Ct Cf Wt Wf Tt Tf

/-- A derivation as a derivation with exit: its exit, or the exit condition `false`
    (`CorresG.ofPlain`). -/
partial def liftG (x : GRes) : GenM (Expr × Expr × SVal × SEnv) := do
  match x.exit with
  | some (C, W, T) => return (x.proof, C, W, T)
  | none =>
    let u ← unitV
    let r ← rapp ``Hax.Ascent.CorresG.ofPlain
    r.set `h x.proof; r.set `W (← lamV u); r.set `T (← lamL x.N)
    return (← r.done, falseE, u, x.N)

/-- The result of a two-way branch on `B` whose derivation `h` states every component as
    the conditional of the branches' components: the values and bindings are merged, and
    the exit condition simplified. -/
partial def iteTail (B h : Expr) (rt rf : GRes) (Ct Cf : Expr) (Wt Wf : SVal)
    (Tt Tf : SEnv) : GenM GRes := do
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

/-- The `Option` match `match o with | some v => e₂ | none => e₁` on a variable
    (`corresG_optMatch`): the `Some` arm binds `v` to `(O).getD default`, and the result
    is the conditional on `(O).isSome`. -/
partial def genMatch (Γ : SEnv) (G _e s arms : Expr) (hint? : Option Expr) : GenM GRes := do
  if let some [a] ← listElems? arms then
    if let (``Prod.mk, #[_, _, p, body]) := (← whnfR a).getAppFnArgs then
      if let (``Hax.ImpPat.tuplePat, #[psE]) := (← instantiateMVars p).getAppFnArgs then
        return ← genMatchTuple Γ G s psE body hint?
  let (``Hax.ImpExpr.var, #[oE]) := (← instantiateMVars s).getAppFnArgs
    | throwError "construct: match_ on a non-variable"
  let some os := strOf? (← instantiateMVars oE) | throwError "construct: match_ variable"
  let some [a1, a2] ← listElems? arms | throwError "construct: match_ arms"
  let (``Prod.mk, #[_, _, p1, e2]) := (← whnfR a1).getAppFnArgs
    | throwError "construct: match_ arm"
  let (``Prod.mk, #[_, _, p2, e1]) := (← whnfR a2).getAppFnArgs
    | throwError "construct: match_ arm"
  let (``Hax.ImpPat.somePat, #[pv]) := (← instantiateMVars p1).getAppFnArgs
    | throwError "construct: match_ pattern"
  let (``Hax.ImpPat.varPat, #[vE]) := (← instantiateMVars pv).getAppFnArgs
    | throwError "construct: match_ pattern"
  unless (← instantiateMVars p2).isConstOf ``Hax.ImpPat.nonePat do
    throwError "construct: match_ pattern"
  let some vs := strOf? (← instantiateMVars vE) | throwError "construct: match_ binder"
  let some sv := lookupEnv Γ os | throwError "unbound: {os}"
  let (some oTy, some O) := (sv.ty?, sv.tm?) | throwError "type: match_ scrutinee"
  let oTy ← whnfR oTy
  unless oTy.isAppOfArity ``Option 1 do throwError "type: match_ scrutinee"
  let α := oTy.appArg!
  let payload ← mkAppM ``Option.getD #[O, ← mkAppOptM ``Inhabited.default #[α, none]]
  let B ← mkAppM ``Option.isSome #[O]
  let Gs ← abstE (andE (← atState G) (← mkEq B trueE))
  let Gn ← abstE (andE (← atState G) (← mkEq B falseE))
  let rs ← gen ((vs, ← typedV α payload) :: Γ) Gs e2 hint?
  let rn ← gen Γ Gn e1 hint?
  let (ps, Cs, Ws, Ts) ← liftG rs
  let (pn, Cn, Wn, Tn) ← liftG rn
  let r ← rapp ``Hax.Ascent.corresG_optMatch
  r.set `α α; r.set `O (← abstE O); r.set `o oE; r.set `v vE; r.set `e2 e2; r.set `e1 e1
  r.set `Cs (← abstE Cs); r.set `Cn (← abstE Cn)
  r.set `hs ps; r.set `hn pn
  r.side `ho
  let h ← r.done
  if rs.exit.isSome || rn.exit.isSome then
    return ← iteTail B h rs rn Cs Cn Ws Wn Ts Tn
  -- no exit: the exit condition `if B then false else false` is `false`
  let k ← rapp ``Hax.Ascent.corresG_congrC
  k.set `h h; k.set `C' (← abstE falseE)
  let hcTy ← k.goal `hC
  let st := (← read).st
  let pfC ← forallTelescope hcTy fun xs _ => do
    let ps ← st.proj xs[0]!
    mkLambdaFVars xs ((← mkAppM ``Hax.Ascent.ite_same #[B, falseE]).replaceFVars st.vars ps)
  k.set `hC pfC
  let p ← rapp ``Hax.Ascent.CorresG.plain
  p.set `h (← k.done)
  let V ← mergeVal B rs.val rn.val
  let N ← mergeEnv B rs.N rn.N
  let c ← rapp ``Hax.Ascent.corresB_conseqVN
  c.set `h (← p.done); c.set `V' (← lamV V); c.set `N' (← lamL N); c.side `hV; c.side `hN
  return { proof := ← c.done, val := V, N }

/-- The match `match s with | (x₁, …, xₙ) => e` (`corresB_matchTuple`): the scrutinee is
    a tuple of `n` components, typed or a `.tuple` literal, and the arm runs with `xᵢ`
    bound to the `i`-th component. A component typed `Boxed α` is bound at `α`. -/
partial def genMatchTuple (Γ : SEnv) (G s psE body : Expr) (hint? : Option Expr) :
    GenM GRes := do
  let some ps ← listElems? psE | throwError "construct: match_ tuple pattern"
  let xs ← ps.mapM fun q => do
    let (``Hax.ImpPat.varPat, #[n]) := (← instantiateMVars q).getAppFnArgs
      | throwError "construct: match_ tuple pattern component"
    let some x := strOf? (← instantiateMVars n) | throwError "construct: match_ binder"
    pure x
  let rs ← gen Γ G s
  if rs.exit.isSome then throwError "construct: exit in a match_ scrutinee"
  let comps : List SVal ← match rs.val.ty?, rs.val.tm? with
    | some ty, some tm => do
      let mut out := []
      let mut ty := ty
      let mut tm := tm
      for k in [0:xs.length] do
        if k + 1 == xs.length then
          let ty' ← whnfR ty
          let (cty, ctm) := if ty'.isAppOfArity ``Hax.Ascent.Boxed 1 then (ty'.appArg!, tm)
            else (ty, tm)
          out := out ++ [← typedV cty ctm]
        else
          let (``Prod, #[α, β]) := (← whnfR ty).getAppFnArgs
            | throwError "type: match_ scrutinee has fewer than {xs.length} components"
          out := out ++ [← typedV α (← mkAppM ``Prod.fst #[tm])]
          tm ← mkAppM ``Prod.snd #[tm]
          ty := β
      pure out
    | _, _ => do
      let (``Hax.Value.tuple, #[l]) := (← instantiateMVars rs.val.val).getAppFnArgs
        | throwError "type: match_ scrutinee"
      let some vs ← listElems? l | throwError "type: match_ scrutinee"
      unless vs.length == xs.length do throwError "type: match_ scrutinee arity"
      vs.mapM fun v => readLeafVal v
  let mut Γb := rs.N
  for x in xs, c in comps do
    Γb := (x, c) :: Γb
  let rb ← gen Γb G body hint?
  let VsE ← abstE (← mkListLit (mkConst ``Hax.Value) (comps.map (·.val)))
  let r ← rapp ``Hax.Ascent.corresB_matchTuple
  r.set `hs rs.proof; r.set `ps psE
  r.set `xs (← mkListLit (mkConst ``String) (xs.map mkStrLit))
  r.set `Vs VsE
  r.side `hW; r.side `hps; r.side `hlen
  r.set `hbody rb.proof
  return { rb with proof := ← r.done }

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

partial def genArgs (Γ : SEnv) (G : Expr) (hints : List (Option Expr) := []) :
    List Expr → GenM (Expr × Array SVal × SEnv)
  | [] => do
    let r ← rapp ``Hax.Ascent.corresArgsB_nil
    r.set `bi (← read).bi; r.set `Γ (← lamL Γ); r.set `G G
    return (← r.done, #[], Γ)
  | a :: as => do
    let ra ← gen Γ G a hints.head?.join
    if ra.exit.isSome then throwError "construct: exit in an argument"
    let (pr, vs, Nend) ← genArgs ra.N G hints.tail as
    let r ← rapp ``Hax.Ascent.corresArgsB_cons
    r.set `he ra.proof; r.set `hes pr; r.side `hplain
    return (← r.done, #[ra.val] ++ vs, Nend)

partial def genApp (Γ : SEnv) (G _e f as : Expr) (hint? : Option Expr) : GenM GRes := do
  let some fs := strOf? (← instantiateMVars f) | throwError "construct: call name"
  let some argEs ← listElems? as | throwError "construct: argument list"
  let (pa, vs, Nend) ← genArgs Γ G (← leafArgHints fs argEs.length) argEs
  let errs ← IO.mkRef (#[] : Array String)
  let some (pf, sv) ← (do
      match ← matchLeaf fs vs hint? true (pend := true) with
      | some x => pure (some x)
      | none =>
        match ← matchLeaf fs vs hint? false (pend := true) (errs? := some errs) with
        | some x => pure (some x)
        | none =>
          match ← matchTagged fs vs with
          | some x => pure (some x)
          | none => matchArrayLit fs vs hint?)
    | throwError "leaf: {fs} {(← errs.get).toList.take 3}"
  let r ← rapp ``Hax.Ascent.corresB_app
  r.set `hargs pa; r.set `f f; r.set `V (← lamV sv)
  let hbiTy ← r.goal `hbi
  let st := (← read).st
  -- the array facts the leaf leaves open, proved from the guard at the current state
  let pending ← getMVars pf
  let mut pendPfs : Array (MVarId × Expr) := #[]
  if !pending.isEmpty then
    let req? := (← read).req?
    let Gσ ← atState G
    for m in pending do
      let ty ← instantiateMVars (← m.getType)
      -- the facts of the guard: a hypothesis is admitted once the derivation has asked
      -- for a fact past them, since it is then derived again
      let n₀ ← match req? with
        | some { base := some b, .. } => b.get
        | some req => pure (← req.need.get).size
        | none => pure 0
      let p ← withLocalDeclD `hG Gσ fun hG => do
        try mkLambdaFVars #[hG] (← proveArr req? ty (← splitFacts hG))
        catch ex =>
          -- a hypothesis that asked for new guard facts is admitted, so that the
          -- derivation collects the other guard facts it asks for; `ascendFn` discards
          -- it and derives the function again under the larger guard
          let some req := req? | throw ex
          unless (← req.need.get).size > n₀ do throw ex
          mkLambdaFVars #[hG] (← mkSorry ty (synthetic := true))
      pendPfs := pendPfs.push (m, p)
  let pfl ← forallTelescope hbiTy fun xs _ => do
    let ps ← st.proj xs[0]!
    let mut body := pf.replaceFVars st.vars ps
    for (m, p) in pendPfs do
      let p' := (p.replaceFVars st.vars ps).beta #[xs[1]!]
      body := body.replace fun e => if e.isMVar && e.mvarId! == m then some p' else none
    mkLambdaFVars xs body
  r.set `hbi pfl
  return { proof := ← r.done, val := sv, N := Nend }

partial def genTuple (Γ : SEnv) (G _e es : Expr) : GenM GRes := do
  let some elems ← listElems? es | throwError "construct: tuple list"
  let (pa, vs, Nend) ← genArgs Γ G [] elems
  let r ← rapp ``Hax.Ascent.corresB_tuple
  r.set `h pa
  let h ← r.done
  let tys := vs.toList.filterMap (·.ty?)
  let tms := vs.toList.filterMap (·.tm?)
  if vs.size ≥ 2 && tys.length == vs.size then
    -- a last component of product type is one component of the tuple
    let tys ← if ← isProdTy tys.getLast! then
        pure (tys.dropLast ++ [← mkAppM ``Hax.Ascent.Boxed #[tys.getLast!]])
      else pure tys
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
  let ra ← gen Γ G a (← read).retTy?
  if ra.exit.isSome then throwError "construct: exit in a break value"
  let r ← rapp ``Hax.Ascent.corresG_cfBreak
  r.set `h ra.proof; r.side `hp
  return { proof := ← r.done, val := ← unitV, N := ra.N, exit := some (trueE, ra.val, ra.N) }

/-- The accumulator variables whose type after the body differs from their type before
    the loop: a body that rebinds a name to a value of another type. -/
partial def retypedAcc (M : List (String × SVal)) (tys : List Expr) (N : SEnv) :
    GenM (List String) := do
  let mut out := []
  for (k, _) in M, t in tys do
    match (lookupEnv N k).bind (·.ty?) with
    | some t' => unless ← isDefEq t t' do out := out ++ [k]
    | none => out := out ++ [k]
  return out

/-- A counted loop. `drop` names the bindings left out of the invariant: the variables
    the body rebinds at another type, which the invariant cannot carry. The accumulator
    invariant `J` states that array components are nonempty and that the components that
    are arrays of arrays have nonempty elements, for those components where this holds
    initially and is kept by the body. It states the same of the arrays of non-integer
    elements inside the components (through `Prod`) and of the arrays inside their
    elements (`AllP`), and, where such a fact does not hold initially and the array is not
    built by a constructor, that it holds of the accumulator when it holds of the initial
    value. `jdrop` names the facts left out, by accumulator and key. -/
partial def genForFold (Γ : SEnv) (G _e var lo hi body : Expr) (rev : Bool := false)
    (drop : List String := []) (jdrop : List (String × String) := []) : GenM GRes := do
  let some vs := strOf? (← instantiateMVars var) | throwError "construct: loop variable"
  let rlo ← gen Γ G lo
  let rhi ← gen rlo.N G hi
  let (some loT, some hiT) := (rlo.val.tm?, rhi.val.tm?) | throwError "type: loop bounds"
  if rlo.exit.isSome || rhi.exit.isSome then throwError "construct: exit in loop bounds"
  let D := (dedupEnv rhi.N []).filter fun p => p.1 != vs && !drop.contains p.1
  let bound ← boundNames body
  let M := (D.filter (bound.contains ·.1)).reverse
  let tys ← M.mapM fun (k, v) => match v.ty? with
    | some t => pure t
    | none => throwError "type: loop accumulator {k}"
  let A ← mkProdTy tys
  let a₀ ← mkTuple (M.map fun p => p.2.tm?.get!)
  let st := (← read).st
  -- the accumulator facts that hold initially
  -- the accumulator facts, by component, name, key and predicate
  let jc ← if rev then pure [] else accFactCands (← atState G) M tys jdrop
  withLocalDeclD `i intTy fun i => withLocalDeclD `acc A fun acc => do
    let comps ← tupleComps acc M.length
    let Jbody := andList (← jc.mapM fun (j, _, _, P) => pure (P.beta #[comps[j]!]))
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
    let bounds := andE (← mkAppM ``LE.le #[loT, i]) (← mkAppM ``LT.lt #[i, hiT])
    let GbE := if jc.isEmpty then andE Gσ bounds else andE (andE Gσ bounds) Jbody
    let Gb ← withReader ({ · with st := bst }) (abstE GbE)
    let rb ← withReader ({ · with st := bst }) (gen Γb Gb body)
    let mut bad ← retypedAcc M tys rb.N
    if let some (_, _, Tb) := rb.exit then
      bad := bad ++ (← retypedAcc M tys Tb)
    unless bad.isEmpty do
      return ← genForFold Γ G _e var lo hi body rev (drop ++ bad.eraseDups) jdrop
    -- the accumulator facts the body keeps
    if !jc.isEmpty then
      let tmsN ← M.mapM fun (k, _) => do
        let some sv := lookupEnv rb.N k | throwError "loop: {k} unbound after the body"
        let some tm := sv.tm? | throwError "type: loop accumulator {k} after the body"
        pure tm
      let lost ← withLocalDeclD `hJ GbE fun hJ => do
        let fs ← splitFacts hJ
        jc.filterM fun (j, _, _, P) => do
          let s ← (Meta.saveState : MetaM Meta.SavedState)
          try
            discard <| proveArr none (P.beta #[tmsN[j]!]) fs
            pure false
          catch _ =>
            (s.restore : MetaM Unit)
            pure true
      unless lost.isEmpty do
        return ← genForFold Γ G _e var lo hi body rev drop
          (jdrop ++ lost.map fun (_, k, key, _) => (k, key))
    let Jl ← withLocalDeclD `s st.stTy fun s => do
      mkLambdaFVars #[s, acc] (Jbody.replaceFVars st.vars (← st.proj s))
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
      let r ← rapp (if rev then ``Hax.Ascent.corresB_forFoldRevP
        else if jc.isEmpty then ``Hax.Ascent.corresB_forFoldP else ``Hax.Ascent.corresB_forFoldPJ)
      if !jc.isEmpty then r.set `J Jl
      setCommon r
      r.side `hinit; r.side `hfresh; r.side `hV; r.side `hstep
      unless jc.isEmpty do
        r.side `hinitJ
        r.side `hJ
      let pf ← r.done
      let gσ := (← lam3 gTm).beta #[st.stVal]
      let fold ← mkAppM (if rev then ``Hax.foldRangeRev else ``Hax.foldRange) #[loT, hiT, a₀, gσ]
      let N ← Λenv.mapM fun (k, v) => do return (k, ← instSValRepl v acc fold)
      return { proof := pf, val := ← unitV, N }
    | some (Cb, Wb, Tb) =>
      if rev then throwError "construct: forFoldRev with break"
      let some wTm := Wb.tm? | throwError "type: break value"
      let gbTm ← accOf Tb
      let r ← rapp (if jc.isEmpty then ``Hax.Ascent.corresB_forFoldG
        else ``Hax.Ascent.corresB_forFoldGJ)
      if !jc.isEmpty then r.set `J Jl
      setCommon r
      r.set `w (← lam3 wTm); r.set `gb (← lam3 gbTm); r.set `Cb (← bodyAbst Cb)
      r.side `hinit; r.side `hfresh; r.side `hW; r.side `hV; r.side `hT; r.side `hN
      unless jc.isEmpty do
        r.side `hinitJ
        r.side `hJ
      let pf ← r.done
      let stepFn ← mkLambdaFVars #[i, acc] (← mkAppM ``Hax.Ascent.stepCF #[Cb, wTm, gbTm, gTm])
      let fold ← mkAppM ``Hax.forFold #[loT, hiT, a₀, stepFn]
      let stE ← mkAppM ``Hax.Ascent.cfState #[fold]
      let N ← Λenv.mapM fun (k, v) => do return (k, ← instSValRepl v acc stE)
      return { proof := pf, val := { val := ← mkAppM ``Hax.Ascent.cfVal #[fold] }, N }

/-- A counted loop with early return (`corresG_forFoldReturnG`): the accumulator and
    invariant are those of `genForFold`, an exit of the body is a return from the
    function, and the loop exits when `Hax.forFoldReturn` returns. -/
partial def genForFoldReturn (Γ : SEnv) (G _e var lo hi body : Expr)
    (drop : List String := []) : GenM GRes := do
  let some vs := strOf? (← instantiateMVars var) | throwError "construct: loop variable"
  let rlo ← gen Γ G lo
  let rhi ← gen rlo.N G hi
  let (some loT, some hiT) := (rlo.val.tm?, rhi.val.tm?) | throwError "type: loop bounds"
  if rlo.exit.isSome || rhi.exit.isSome then throwError "construct: exit in loop bounds"
  let D := (dedupEnv rhi.N []).filter fun p => p.1 != vs && !drop.contains p.1
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
    let bodyAbst (x : Expr) : GenM Expr := withReader ({ · with st := bst }) (abstE x)
    let bad ← retypedAcc M tys rb.N
    unless bad.isEmpty do
      return ← genForFoldReturn Γ G _e var lo hi body (drop ++ bad)
    let tms ← M.mapM fun (k, _) => do
      let some sv := lookupEnv rb.N k | throwError "loop: {k} unbound after the body"
      let some tm := sv.tm? | throwError "type: loop accumulator {k} after the body"
      pure tm
    let gTm ← mkTuple tms
    -- the body exit is the return; a body without exit never returns
    let (pb, Cb, wTm, R) ← match rb.exit with
      | some (Cb, Wb, _) => do
        let (some wTm, some R) := (Wb.tm?, Wb.ty?) | throwError "type: return value"
        pure (rb.proof, Cb, wTm, R)
      | none => do
        let u ← unitV
        let r ← rapp ``Hax.Ascent.CorresG.ofPlain
        r.set `h rb.proof; r.set `W (← bodyAbst u.val); r.set `T (← bodyAbst (mkBList rb.N))
        pure (← r.done, falseE, mkConst ``Unit.unit, mkConst ``Unit)
    let r ← rapp ``Hax.Ascent.corresG_forFoldReturnG
    r.set `R R
    r.set `hlo rlo.proof; r.set `hhi rhi.proof
    r.set `var var; r.set `body body
    r.set `a₀ (← abstE a₀); r.set `g (← lam3 gTm); r.set `Λ Λl
    r.set `w (← lam3 wTm); r.set `Cb (← bodyAbst Cb)
    r.set `hbody pb
    r.side `hinit; r.side `hfresh; r.side `hW; r.side `hV; r.side `hN
    let pf ← r.done
    let stepFn ← mkLambdaFVars #[i, acc] (← mkAppM ``Hax.Ascent.stepRet #[Cb, wTm, gTm])
    let fold ← mkAppM ``Hax.forFoldReturn #[loT, hiT, a₀, stepFn]
    let C ← mkAppM ``Hax.Ascent.retC #[fold]
    let d := wTm.replaceFVars #[i, acc] #[loT, a₀]
    let W ← typedV R (← mkAppM ``Hax.Ascent.retOut #[d, fold])
    let accE ← mkAppM ``Hax.Ascent.retAcc #[a₀, fold]
    let N ← Λenv.mapM fun (k, v) => do return (k, ← instSValRepl v acc accE)
    return { proof := pf, val := ← unitV, N, exit := some (C, W, []) }

/-- Replace a free variable in a symbolic value. -/
partial def instSValRepl (v : SVal) (x r : Expr) : MetaM SVal := do
  return { val := v.val.replaceFVar x r, ty? := v.ty?.map (·.replaceFVar x r),
           tm? := v.tm?.map (·.replaceFVar x r) }

/-- A while loop. Its accumulator invariant `J` (`corresB_whileFoldGJ`) holds the facts of
    `accFactCands`, with the sign of integer components, that hold initially and are kept by
    the body; `jdrop` names the facts left out. -/
partial def genWhile (Γ : SEnv) (G _e cond body : Expr) (jdrop : List (String × String) := []) :
    GenM GRes := do
  let D := dedupEnv Γ []
  let bound := (← boundNames body) ++ (← boundNames cond)
  let M := (D.filter (bound.contains ·.1)).reverse
  let tys ← M.mapM fun (k, v) => match v.ty? with
    | some t => pure t
    | none => throwError "type: loop accumulator {k}"
  let A ← mkProdTy tys
  let a₀ ← mkTuple (M.map fun p => p.2.tm?.get!)
  let st := (← read).st
  let Gσ0 ← atState G
  let jc ← accFactCands Gσ0 M tys jdrop (ints := true)
  withLocalDeclD `acc A fun acc => do
    let comps ← tupleComps acc M.length
    let Jbody := andList (jc.map fun (j, _, _, P) => P.beta #[comps[j]!])
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
      let GcE := andE Gσ0 (← mkEq cTm trueE)
      let GbE := if jc.isEmpty then GcE else andE GcE Jbody
      let Gb ← abstE GbE
      let rb0 ← gen rc.N Gb body
      let accTms (env : SEnv) : MetaM (List Expr) := M.mapM fun (k, _) => do
        let some sv := lookupEnv env k | throwError "loop: {k} unbound after the body"
        let some tm := sv.tm? | throwError "type: loop accumulator {k} after the body"
        pure tm
      let accOf (env : SEnv) : MetaM Expr := do mkTuple (← accTms env)
      -- the accumulator facts the body keeps
      if !jc.isEmpty then
        let tmsN ← accTms rb0.N
        let lost ← withLocalDeclD `hJ GbE fun hJ => do
          let fs ← splitFacts hJ
          jc.filterM fun (j, _, _, P) => do
            let s ← (Meta.saveState : MetaM Meta.SavedState)
            try
              discard <| proveArr none (P.beta #[tmsN[j]!]) fs
              pure false
            catch _ =>
              (s.restore : MetaM Unit)
              pure true
        unless lost.isEmpty do
          return ← (genWhile Γ G _e cond body
            (jdrop ++ lost.map fun (_, k, key, _) => (k, key))).run { (← read) with st := st }
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
      let r ← rapp (if jc.isEmpty then ``Hax.Ascent.corresB_whileFoldG
        else ``Hax.Ascent.corresB_whileFoldGJ)
      if !jc.isEmpty then
        r.set `J (← withLocalDeclD `s st.stTy fun s => do
          mkLambdaFVars #[s, acc] (Jbody.replaceFVars st.vars (← st.proj s)))
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
      unless jc.isEmpty do
        r.side `hinitJ
        r.side `hJ
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
    comparisons of its condition and exit condition. Each measure is tried within a
    twentieth of the heartbeat budget (`boundedTryT`). -/
partial def proveTerm (ty : Expr) : GenM Expr := do
  forallTelescope ty fun xs body => do
    let body ← instantiateMVars body
    let (``Hax.WhileFoldStops, #[α, _, init, c, f]) := body.getAppFnArgs
      | throwError "loop: termination goal{shortExpr body}"
    let cands ← measureCands α c f
    let mut lastErr := ""
    for μ in cands do
      let r ← boundedTryT do
        let hdec ← termDecrease α c f μ
        let pf ← mkAppM ``Hax.Ascent.whileFoldStops_of_measure #[μ, hdec, init]
        mkLambdaFVars xs (← mkExpectedTypeHint pf body)
      match r with
      | .ok pf => return pf
      | .error m => lastErr := m
    throwError "loop: while termination not proved ({cands.length} measures; {lastErr})"

/-- Candidate measures for the comparisons `x < y`, `x ≤ y` of the loop's condition and
    step: `fun a => (y - x).toNat` and `fun a => (y - x + 1).toNat` for each comparison, in
    both directions, and the sums `(y₁ - x₁).toNat + (y₂ - x₂).toNat` over two
    comparisons, for a loop whose step advances one of two counters. With several
    comparisons the sum of all their gaps comes first. -/
partial def measureCands (α c f : Expr) : MetaM (List Expr) := do
  withLocalDeclD `a α fun a => do
    let body ← instantiateMVars (mkApp2 (mkConst ``_root_.And) (← mkEq (c.beta #[a]) trueE)
      (← mkEq (f.beta #[a]) (f.beta #[a])))
    let mut cmps : Array (Expr × Expr × Bool) := #[]
    for sub in collectCmp body do
      let (x, y, _) := sub
      if (x.containsFVar a.fvarId! || y.containsFVar a.fvarId!) && !cmps.contains sub then
        cmps := cmps.push sub
    let mut out := []
    for (x, y, _) in cmps do
      for (p, q) in [(x, y), (y, x)] do
        for d in [(← mkAppM ``HSub.hSub #[q, p]), (← mkAppM ``HAdd.hAdd #[← mkAppM ``HSub.hSub #[q, p], mkIntLit 1])] do
          out := out ++ [← mkLambdaFVars #[a] (← mkAppM ``Int.toNat #[d])]
    let gap (cmp : Expr × Expr × Bool) : MetaM Expr := do
      let (x, y, strict) := cmp
      let d ← mkAppM ``HSub.hSub #[y, x]
      mkAppM ``Int.toNat #[← if strict then pure d else mkAppM ``HAdd.hAdd #[d, mkIntLit 1]]
    for i in [0:cmps.size] do
      for j in [i+1:cmps.size] do
        out := out ++ [← mkLambdaFVars #[a] (← mkAppM ``HAdd.hAdd #[← gap cmps[i]!, ← gap cmps[j]!])]
    -- the sum of all gaps first: it decreases whenever the step advances some counter and
    -- moves none back
    if cmps.size > 2 then
      let gs ← cmps.toList.mapM gap
      let all ← gs.tail.foldlM (fun s g => mkAppM ``HAdd.hAdd #[s, g]) gs.head!
      out := (← mkLambdaFVars #[a] all) :: out
    else if cmps.size == 2 then
      out := out.getLast! :: out.dropLast
    return out
where
  mkIntLit (n : Nat) : Expr := toExpr (n : Int)
  /-- The integer comparisons as `(lo, hi, strict)`: `lo < hi` when `strict`, else
      `lo ≤ hi`. -/
  collectCmp (e : Expr) : List (Expr × Expr × Bool) :=
    let here := match e.getAppFnArgs with
      | (``Hax.lt, #[ty, _, _, x, y]) => if ty.isConstOf ``Int then [(x, y, true)] else []
      | (``Hax.le, #[ty, _, _, x, y]) => if ty.isConstOf ``Int then [(x, y, false)] else []
      | (``Hax.gt, #[ty, _, _, x, y]) => if ty.isConstOf ``Int then [(y, x, true)] else []
      | (``Hax.ge, #[ty, _, _, x, y]) => if ty.isConstOf ``Int then [(y, x, false)] else []
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

/-- The runtime leaf lemmas of `HaxAscent/Ascent/RuntimeOps.lean`, in source order. -/
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
  /-- The type a parameter or result of a surface type is encoded at: a struct type in
      its encoded form (`Boxed` last field). -/
  normTy : Expr → MetaM Expr := pure
  /-- The precondition, a predicate of the argument tuple; `none` for `True`. Its
      conjuncts are the first facts of the guard, so that every side condition of the
      derivation is proved under them. -/
  pre? : Option Expr := none

/-- The conjuncts of a right-nested conjunction, read syntactically after
    beta-reduction: `andList (conjuncts p)` is `p`. -/
partial def conjuncts (p : Expr) : List Expr :=
  let p := p.headBeta
  if p.isAppOfArity ``_root_.And 2 then p.getArg! 0 :: conjuncts (p.getArg! 1) else [p]

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
  /-- The guard of the correspondence, a predicate of the argument tuple: the conjuncts of
      the precondition `FnSpec.pre?`, followed by the nonemptiness facts about the arguments
      the derivation asks for, `True` for none. -/
  guard : Expr

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
    let tys ← xs.toList.mapM fun x => do spec.normTy (← inferType x)
    let retTy ← spec.normTy retTy
    let A ← argTupleTy tys
    withLocalDeclD `a A fun a => do
      let comps ← argComps a tys.length
      let mut Γ₀ : SEnv := []
      for p in spec.params, t in tys, c in comps do
        Γ₀ := Γ₀ ++ [(p, ← typedV t c)]
      for (g, sv, _) in spec.globals do
        Γ₀ := Γ₀ ++ [(g, sv)]
      let st : StCtx := { stTy := A, vars := #[a], proj := fun t => pure #[t], stVal := a }
      -- the guard starts from the conjuncts of the precondition
      let pre : Array Expr := match spec.pre? with
        | some P => (conjuncts (P.beta #[a])).toArray
        | none => #[]
      let need ← IO.mkRef pre
      let base ← IO.mkRef 0
      let ints ← (comps.zip tys).filterMapM fun (c, t) => do
        return if ← isDefEq t intTy then some c else none
      let ctx : GCtx := { bi := spec.bi, st, leaves := spec.leaves, hints := spec.hints,
                          retTy? := some retTy,
                          req? := some { top := a, need, ints := ints.toArray, base := some base } }
      -- the guard: the facts about the arguments the derivation asks for, derived again
      -- while it asks for more
      let mut attempt : Nat := 0
      let mut res? : Option (Expr × GRes) := none
      while res?.isNone do
        let facts ← need.get
        base.set facts.size
        let G ← mkLambdaFVars #[a] (andList facts.toList)
        let s ← saveState
        try
          let r ← (gen Γ₀ G spec.lit (some retTy)).run ctx
          -- a derivation that admitted a hypothesis asking for new guard facts is derived
          -- again under the larger guard
          if (← instantiateMVars r.proof).hasSorry then
            throwError "guard: {(← need.get).size - facts.size} new facts"
          res? := some (G, r)
        catch ex =>
          attempt := attempt + 1
          unless (← need.get).size > facts.size && attempt < 8 do throw ex
          s.restore
      let some (G, r) := res? | throwError "hax_ascend: internal: guard"
      let Γ₀l ← (lamL Γ₀).run ctx
      let (entry, hentry0) ← spec.entry A Γ₀l
      let hentry ← if (← need.get).isEmpty then pure hentry0 else
        withLocalDeclD `a A fun a' => withLocalDeclD `h (G.beta #[a']) fun h => do
          mkLambdaFVars #[a', h] (mkApp2 hentry0 a' (mkConst ``True.intro))
      let surfaceApp := mkAppN spec.surface comps.toArray
      let surfaceFn ← mkLambdaFVars #[a] surfaceApp
      match r.exit with
      | none =>
        let some tm := r.val.tm? | throwError "type: result value"
        let some β := r.val.ty? | throwError "type: result value"
        -- the result type, when it differs from the type of the term (`Boxed`)
        let tmβ ← if ← withReducible (isDefEq (← inferType tm) β) then pure tm
          else mkExpectedTypeHint tm β
        let fn ← mkLambdaFVars #[a] tmβ
        let k ← rapp ``Hax.Ascent.fnCorres_of_corresB
        k.set `β β
        k.set `h r.proof; k.set `entry entry; k.set `f fn; k.set `hentry hentry
        k.side `hV
        let thm ← k.done
        let thmTy ← instantiateMVars (← inferType thm)
        let oracle ← (do
          unless ← isDefEq β retTy do return false
          withTransparency .default (isDefEqBounded tm surfaceApp))
        return { argTy := A, fn, thmTy, thm, merged? := none, surfaceFn, oracle, guard := G }
      | some (C, W, _) =>
        let (some wTm, some vTm, some βw, some β) := (W.tm?, r.val.tm?, W.ty?, r.val.ty?)
          | throwError "type: result value"
        let k ← rapp ``Hax.Ascent.fnCorresX_of_corresG
        -- the result type of the exit value (`Boxed` components), not the type of the term
        k.set `β βw
        k.set `h r.proof; k.set `entry entry; k.set `hentry hentry
        let atβw (t : Expr) : MetaM Expr := do
          if ← withReducible (isDefEq (← inferType t) βw) then pure t
          else mkExpectedTypeHint t βw
        k.set `w (← mkLambdaFVars #[a] (← atβw wTm))
        k.set `v (← mkLambdaFVars #[a] (← atβw vTm))
        k.side `hW; k.side `hV
        let thm ← k.done
        let thmTy ← instantiateMVars (← inferType thm)
        let exc ← mkAppOptM ``Except.error #[βw, βw, wTm]
        let ok ← mkAppOptM ``Except.ok #[βw, βw, vTm]
        let fn ← mkLambdaFVars #[a] (← mkIteB C exc ok)
        let mut merged? := none
        let mut oracle := false
        if ← isDefEq βw β then
          let m ← atβw (← mkIteB C wTm vTm)
          merged? := some (← mkLambdaFVars #[a] m)
          oracle ← (do
            unless ← isDefEq β retTy do return false
            withTransparency .default (isDefEqBounded m surfaceApp))
        let parts := (← mkLambdaFVars #[a] C, ← mkLambdaFVars #[a] wTm, ← mkLambdaFVars #[a] vTm)
        return { argTy := A, fn, thmTy, thm, merged?, surfaceFn, oracle, parts? := some parts,
                 guard := G }

end Hax.Ascent.Gen

end

end
