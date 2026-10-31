/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.TExpr
public import HaxLean.Phase.InlineLocalClosures

/-!
# Typing facts and the statement spine of a body

The typing facts of a typed body (`texprFacts`) and the common type of a list of types
(`tyAgree`), and the steps of the statement-spine reading `denoteSpine` at a binding and at
a sequence.

## Main definitions

* `TyFact`, `ctorFact`, `isArrUpdate`, `isVarOf`, `texprFacts` — the typing facts of a typed
  body
* `stripRef`, `tyAgree`, `factNameTys` — the common type of a list of types and the types the
  facts give a name
* `isLamE`, `spineLamFree` — a closure, and a body whose spine binds no closure
* `spineLetStep`, `spineSeqStep` — the steps of `denoteSpine` after a bound value and after
  a first statement

## Main results

* `denoteSpine_letBind`, `denoteSpine_seq` — `denoteSpine` at a binding of a value that is
  no closure and at a sequence
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpType ImpPat TExpr Env Outcome Builtins denote')
open _root_.Hax.InlineLocalClosures (denoteSpine)

/-! ## Types of a typed body -/

/-- A typing fact of a typed body: a name has a type, a call of a name has a result
    type, or a call of the constructor `s` of the struct type `.adt s _` has arguments of
    the types `tys`. -/
inductive TyFact where
  | name (x : String) (t : ImpType)
  | call (f : String) (t : ImpType)
  | ctor (s : String) (tys : List ImpType)

/-- The constructor fact of a call of `f` with arguments of the types `tys` and result type
    `t`: `.ctor f tys` when `t` is, up to references, the struct type `.adt f _`. -/
def ctorFact (f : String) (tys : List ImpType) : ImpType → List TyFact
  | .ref t _ => ctorFact f tys t
  | .adt s _ => if s == f then [.ctor f tys] else []
  | _ => []

/-- `v` is an element store `array_update(...)`. -/
def isArrUpdate : TExpr → Bool
  | .mk (.app "array_update" _) _ => true
  | _ => false

/-- The typed expression is the variable `n`. -/
def isVarOf (n : String) : TExpr → Bool
  | .mk (.var m) _ => m == n
  | _ => false

/-- The typing facts of a typed body: the type of every variable occurrence, of the value
    of every `letBind` other than an element store, of every assignment and loop counter,
    the result type of every call, and the argument types of every call of a struct
    constructor (`ctorFact`). The extraction annotates an element store
    `let n = array_update(...)`, and a body `n` of that binding, with the element type,
    so neither gives a fact on `n`. -/
def texprFacts : TExpr → List TyFact
  | .mk (.var n) ty => [.name n ty]
  | .mk (.letBind n v b) _ =>
      if isArrUpdate v then texprFacts v ++ (if isVarOf n b then [] else texprFacts b)
      else .name n v.ty :: (texprFacts v ++ texprFacts b)
  | .mk (.lam _ b) _ => texprFacts b
  | .mk (.app f args) ty => .call f ty :: (ctorFact f (args.map TExpr.ty) ty ++ factsList args)
  | .mk (.tuple es) _ => factsList es
  | .mk (.proj e _) _ => texprFacts e
  | .mk (.ifThenElse c t e) _ => texprFacts c ++ texprFacts t ++ texprFacts e
  | .mk (.match_ s arms) _ => texprFacts s ++ factsArms arms
  | .mk (.seq a b) _ => texprFacts a ++ texprFacts b
  | .mk (.borrow e) _ => texprFacts e
  | .mk (.deref e) _ => texprFacts e
  | .mk (.assign n rhs) _ => .name n rhs.ty :: texprFacts rhs
  | .mk (.forLoop v lo hi b) _ =>
      .name v lo.ty :: (texprFacts lo ++ texprFacts hi ++ texprFacts b)
  | .mk (.forLoopRev v lo hi b) _ =>
      .name v lo.ty :: (texprFacts lo ++ texprFacts hi ++ texprFacts b)
  | .mk (.whileLoop c b) _ => texprFacts c ++ texprFacts b
  | .mk (.break_ (some e)) _ => texprFacts e
  | .mk (.earlyReturn e) _ => texprFacts e
  | .mk (.questionMark e) _ => texprFacts e
  | .mk (.forFold v lo hi b) _ =>
      .name v lo.ty :: (texprFacts lo ++ texprFacts hi ++ texprFacts b)
  | .mk (.forFoldRev v lo hi b) _ =>
      .name v lo.ty :: (texprFacts lo ++ texprFacts hi ++ texprFacts b)
  | .mk (.whileFold c b) _ => texprFacts c ++ texprFacts b
  | .mk (.forFoldReturn v lo hi b) _ =>
      .name v lo.ty :: (texprFacts lo ++ texprFacts hi ++ texprFacts b)
  | .mk (.forFoldRevReturn v lo hi b) _ =>
      .name v lo.ty :: (texprFacts lo ++ texprFacts hi ++ texprFacts b)
  | .mk (.whileFoldReturn c b) _ => texprFacts c ++ texprFacts b
  | .mk (.cfBreak e) _ => texprFacts e
  | .mk (.cfContinue e) _ => texprFacts e
  | .mk (.cfBreakContinue e) _ => texprFacts e
  | .mk (.ann e) _ => texprFacts e
  | .mk (.namedProj _ e) _ => texprFacts e
  | _ => []
where
  /-- The facts of a list of typed expressions. -/
  factsList : List TExpr → List TyFact
    | [] => []
    | e :: es => texprFacts e ++ factsList es
  /-- The facts of the arms of a `match_`. -/
  factsArms : List (ImpPat × TExpr) → List TyFact
    | [] => []
    | (_, e) :: rest => texprFacts e ++ factsArms rest

/-- A type with its references removed. -/
def stripRef : ImpType → ImpType
  | .ref t _ => stripRef t
  | t => t

/-- The common type of a list of types up to references, with the entries `unknown`
    ignored; `unknown` when no entry is known or two known entries differ. -/
def tyAgree (ts : List ImpType) : ImpType :=
  match (ts.map stripRef).filter (· != .unknown) with
  | [] => .unknown
  | t :: ts => if ts.all (· == t) then t else .unknown

/-- The types the facts give the name `x`. -/
def factNameTys (fs : List TyFact) (x : String) : List ImpType :=
  fs.filterMap fun
    | .name y t => if y == x then some t else none
    | _ => none

/-! ## The statement spine -/

/-- The expression is a closure. -/
def isLamE : ImpExpr → Bool
  | .lam _ _ => true
  | _ => false

/-- No binding of the statement spine of `e` binds a closure. -/
def spineLamFree : ImpExpr → Bool
  | .letBind _ v cont => !isLamE v && spineLamFree cont
  | .seq _ b => spineLamFree b
  | _ => true

/-- The step of `denoteSpine` after the value `rv` of the bound expression of
    `let x = v; k`. -/
def spineLetStep (x : String) (rv : Outcome) (k : StateM Env Outcome) : StateM Env Outcome :=
  match rv with
  | .val (.controlFlow isBreak w) => pure (.val (.controlFlow isBreak w))
  | .val w => do modify (_root_.Hax.Env.extend · x w); k
  | other => pure other

/-- The step of `denoteSpine` after the outcome `r` of the first statement of `a; k`. -/
def spineSeqStep (r : Outcome) (k : StateM Env Outcome) : StateM Env Outcome :=
  match r with
  | .val (.controlFlow isBreak w) => pure (.val (.controlFlow isBreak w))
  | .val _ => k
  | other => pure other

/-- `denoteSpine` at a binding of a value that is no closure: the value, then the step
    `spineLetStep`. -/
theorem denoteSpine_letBind (bi : Builtins) (fuel : Nat) (x : String) (v cont : ImpExpr)
    (hv : isLamE v = false) :
    denoteSpine bi fuel (.letBind x v cont) =
      denote' bi fuel v >>= fun rv => spineLetStep x rv (denoteSpine bi fuel cont) := by
  cases v with
  | lam ps body => simp [isLamE] at hv
  | _ => rfl

/-- The unfolding of `denoteSpine` at a sequence. -/
theorem denoteSpine_seq (bi : Builtins) (fuel : Nat) (a b : ImpExpr) :
    denoteSpine bi fuel (.seq a b) =
      denote' bi fuel a >>= fun r => spineSeqStep r (denoteSpine bi fuel b) := rfl

end CatCrypt.Crypto.Hax
