/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxCallNames
public import CatCrypt.Crypto.Jasmin.LowCTSyntax
public import HaxLean.AST

/-!
# Translation `LowCT → Option ImpExpr` into the hax AST: the definitions

`lowCTToImp c` is the hax-lean `ImpExpr` whose lowering by the front
`haxToLowCT` is `c` with the front's located types (`frontNF c`).  The table of
its arms, the round-trip theorems and the description of `frontNF` are in
`CatCrypt.Crypto.Hax.LowCTToHax`, which re-exports this module.

The module also holds the call-name predicates the translation and the front
share: the call names computed in the scalar heap (`scalarCallNames`,
`scalarCallName`) and the arguments of a limb read (`limbReadArgs`).

## Main definitions

* `lowCTToImp` — the translation.
* `frontNF` — the located types of the front's lowering.
* `sexprToImpBound`, `scalarCallOfSExpr`, `limbReadOfSExpr` — the scalar-expression arms.
* `scalarCallName`, `limbReadArgs` — the scalar calls and the limb reads of the front.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpPat)
open CatCrypt.Crypto.Jasmin.LowCT (TowerType LowCT Located SExpr)

/-! ## §1  Call names -/

/-- The call names computed in the scalar heap. -/
def scalarCallNames : List String :=
  ["scalar#Add", "scalar#Sub", "scalar#Mul", "scalar#BitAnd", "scalar#BitXor",
   "scalar#Shr", "scalar#Shl",
   "scalar#Lt", "scalar#Gt", "scalar#Le", "scalar#Ge", "scalar#Eq", "scalar#Ne"]

/-- `f` is a call name computed in the scalar heap. -/
def scalarCallName (f : String) : Bool := scalarCallNames.contains f

/-- The call names computed in the scalar heap are neither `array_update` nor
    `index`. -/
theorem scalarCallName_ne {f : String} (h : scalarCallName f = true) :
    f ≠ "array_update" ∧ f ≠ "index" := by
  constructor <;> (rintro rfl; simp [scalarCallName, scalarCallNames] at h)

/-- The slot and the limb of a limb read: the arguments of a call `index` on a
    variable and a non-negative integer literal. -/
def limbReadArgs (f : String) (args : List ImpExpr) : Option (String × Nat) :=
  if f = "index" then
    match args with
    | [.var v, .lit (.int i)] => if 0 ≤ i then some (v, i.toNat) else none
    | _ => none
  else none

/-- The front reads the call `index` on a variable and the literal of a limb as
    the limb read. -/
theorem limbReadArgs_index (v : String) (i : Nat) :
    limbReadArgs "index" [.var v, .lit (.int i)] = some (v, i) := by
  simp [limbReadArgs]

/-! ## §2  Scalar expressions -/

/-- The hax loop bound of a scalar expression: a variable, a literal, and
    `Add`, `Sub`, `Mul` of bounds.  The inverse of `impBoundToSExpr`. -/
def sexprToImpBound : SExpr → Option ImpExpr
  | .SVar x => some (.var x)
  | .SLit n => some (.lit (.int n))
  | .SAdd a b =>
      match sexprToImpBound a, sexprToImpBound b with
      | some x, some y => some (.app "Add" [x, y])
      | _, _ => none
  | .SSub a b =>
      match sexprToImpBound a, sexprToImpBound b with
      | some x, some y => some (.app "Sub" [x, y])
      | _, _ => none
  | .SMul a b =>
      match sexprToImpBound a, sexprToImpBound b with
      | some x, some y => some (.app "Mul" [x, y])
      | _, _ => none
  | _ => none

/-- The scalar call `(f, a, b)` whose scalar expression `scalarCallSExpr f a b`
    is the given expression, for the shapes that function produces on two
    variables.  `SLt b a`, the expression of `scalar#Gt a b`, is read as
    `scalar#Lt b a`, and `1 - SLt a b`, the expression of `scalar#Ge a b`, as
    `scalar#Le b a`. -/
def scalarCallOfSExpr : SExpr → Option (String × String × String)
  | .SAdd (.SVar a) (.SVar b) => some ("scalar#Add", a, b)
  | .SSub (.SVar a) (.SVar b) => some ("scalar#Sub", a, b)
  | .SMul (.SVar a) (.SVar b) => some ("scalar#Mul", a, b)
  | .SAnd (.SVar a) (.SVar b) => some ("scalar#BitAnd", a, b)
  | .SXor (.SVar a) (.SVar b) => some ("scalar#BitXor", a, b)
  | .SShr (.SVar a) (.SVar b) => some ("scalar#Shr", a, b)
  | .SShl (.SVar a) (.SVar b) => some ("scalar#Shl", a, b)
  | .SLt (.SVar a) (.SVar b) => some ("scalar#Lt", a, b)
  | .SSub (.SLit 1) (.SLt (.SVar b) (.SVar a)) => some ("scalar#Le", a, b)
  | .SSub (.SSub (.SLit 1) (.SLt (.SVar a) (.SVar b))) (.SLt (.SVar b') (.SVar a')) =>
      if a' = a ∧ b' = b then some ("scalar#Eq", a, b) else none
  | .SAdd (.SLt (.SVar a) (.SVar b)) (.SLt (.SVar b') (.SVar a')) =>
      if a' = a ∧ b' = b then some ("scalar#Ne", a, b) else none
  | _ => none

/-- The slot and the limb of a limb read `SLimb v i`. -/
def limbReadOfSExpr : SExpr → Option (String × Nat)
  | .SLimb v i => some (v, i)
  | _ => none

/-! ## §3  The translation -/

/-- The call arguments of a list of slots: the variable of each slot. -/
def locArgsToImp (args : List Located) : List ImpExpr :=
  args.map fun a => .var a.locVar

/-- The slots `args` at the located type `dt`. -/
def retypeArgs (dt : TowerType) (args : List Located) : List Located :=
  args.map fun a => { locVar := a.locVar, locSrc := dt }

/-- The assignment of a bare call `f` into the destination `d`; `none` for
    `array_update` on three arguments, whose assignment the front lowers to an
    array store. -/
@[simp] def callToImp (f : String) (d : Located) (args : List Located) : Option ImpExpr :=
  if f = "array_update" ∧ args.length = 3 then none
  else some (.assign d.locVar (.app f (locArgsToImp args)))

/-- The hax expression that `haxToLowCT` lowers to the command, or `none` when
    no arm of `haxToLowCT` produces the command's shape. -/
def lowCTToImp : LowCT → Option ImpExpr
  | .RSkip => some .unitVal
  | .RSeq (.RArrStore arr idx src) b =>
      (lowCTToImp b).map fun b' =>
        .letBind arr.locVar (.app "array_update" [.var arr.locVar, .var idx, .var src.locVar]) b'
  | .RSeq a b =>
      match lowCTToImp a, lowCTToImp b with
      | some a', some b' => some (.seq a' b')
      | _, _ => none
  | .RScalarSet x k => some (.assign x (.lit (.int k)))
  | .RCall f d args => callToImp f d args
  | .RLetZero x _ (.RSeq (.RCall f d args) b) =>
      if d.locVar = x ∧ f ≠ "array_update" ∧ f ≠ "index" ∧ scalarCallName f = false then
        (lowCTToImp b).map fun b' => .letBind x (.app f (locArgsToImp args)) b'
      else none
  | .RLetZero x _ (.RSeq (.RArrLoad d s idx) b) =>
      if d.locVar = x then
        (lowCTToImp b).map fun b' =>
          .letBind x (.app "index" [.var s.locVar, .var idx]) b'
      else none
  | .RLetZero x _ (.RSeq (.RTupleLoad d s i) b) =>
      if d.locVar = x then
        (lowCTToImp b).map fun b' => .letBind x (.proj (.var s.locVar) i) b'
      else none
  | .RLetZero x _ (.RLetZero y _ (.RSeq (.RCallSwap f d e args) b)) =>
      if d.locVar = x ∧ e.locVar = y then
        (lowCTToImp b).map fun b' =>
          .match_ (.app f (locArgsToImp args)) [(.tuplePat [.varPat x, .varPat y], b')]
      else none
  | .RLetU64Zero x (.RSeq (.RScalarSet y k) b) =>
      if y = x then (lowCTToImp b).map fun b' => .letBind x (.lit (.int k)) b'
      else none
  | .RLetU64Zero x (.RSeq (.RScalarSetExpr y se) b) =>
      match scalarCallOfSExpr se with
      | some (f, a, a2) =>
          if y = x then
            (lowCTToImp b).map fun b' => .letBind x (.app f [.var a, .var a2]) b'
          else none
      | none =>
          match limbReadOfSExpr se with
          | some (v, i) =>
              if y = x then
                (lowCTToImp b).map fun b' =>
                  .letBind x (.app "index" [.var v, .lit (.int i)]) b'
              else none
          | none =>
              match se with
              | .SVar s =>
                  if y = x ∧ s ≠ x then
                    (lowCTToImp b).map fun b' => .letBind x (.var s) b'
                  else none
              | _ => none
  | .RIfNz v t e =>
      match lowCTToImp t, lowCTToImp e with
      | some t', some e' => some (.ifThenElse (.var v) t' e')
      | _, _ => none
  | .RWhileNz v b => (lowCTToImp b).map fun b' => .whileLoop (.var v) b'
  | .RFor x n b => (lowCTToImp b).map fun b' => .forFold x (.lit (.int 0)) (.lit (.int n)) b'
  | .RForRuntime x bound b =>
      match bound with
      | .SLit _ => none
      | _ =>
          match sexprToImpBound bound, lowCTToImp b with
          | some hi, some b' => some (.forFold x (.lit (.int 0)) hi b')
          | _, _ => none
  | .RLetZero x _ (.RSeq (.RCopy d s) b) =>
      if d.locVar = x ∧ s.locVar ≠ x then
        (lowCTToImp b).map fun b' => .letBind x (.var s.locVar) b'
      else none
  | _ => none

/-- The command with the located types and destination names of the front's
    lowering: a call `f` at `towerOfCallName f`, array stores at `.TBytes 0`,
    array and tuple loads at `.TFp`, the destination of a fused binding
    named by the binder, and a whole-slot copy binding as the scalar copy of
    its source, the lowering of `let x = s` by the untyped front.  On every
    command that `lowCTToImp` translates the destination of a fused binding
    already is the binder, so `frontNF` changes located types and copy
    bindings only. -/
def frontNF : LowCT → LowCT
  | .RSkip => .RSkip
  | .RSeq (.RArrStore arr idx src) b =>
      .RSeq (.RArrStore { locVar := arr.locVar, locSrc := .TBytes 0 } idx
        { locVar := src.locVar, locSrc := .TBytes 0 }) (frontNF b)
  | .RSeq a b => .RSeq (frontNF a) (frontNF b)
  | .RCall f d args =>
      .RCall f { locVar := d.locVar, locSrc := towerOfCallName f }
        (retypeArgs (towerOfCallName f) args)
  | .RLetZero x _ (.RSeq (.RCall f _ args) b) =>
      .RLetZero x (towerOfCallName f)
        (.RSeq (.RCall f { locVar := x, locSrc := towerOfCallName f }
          (retypeArgs (towerOfCallName f) args)) (frontNF b))
  | .RLetZero x _ (.RSeq (.RArrLoad _ s idx) b) =>
      .RLetZero x .TFp
        (.RSeq (.RArrLoad { locVar := x, locSrc := .TFp } { locVar := s.locVar, locSrc := .TFp }
          idx) (frontNF b))
  | .RLetZero x _ (.RSeq (.RTupleLoad _ s i) b) =>
      .RLetZero x .TFp
        (.RSeq (.RTupleLoad { locVar := x, locSrc := .TFp } { locVar := s.locVar, locSrc := .TFp }
          i) (frontNF b))
  | .RLetZero x _ (.RLetZero y _ (.RSeq (.RCallSwap f _ _ args) b)) =>
      .RLetZero x (towerOfCallName f) (.RLetZero y (towerOfCallName f)
        (.RSeq (.RCallSwap f { locVar := x, locSrc := towerOfCallName f }
          { locVar := y, locSrc := towerOfCallName f } (retypeArgs (towerOfCallName f) args))
          (frontNF b)))
  | .RLetZero x _ (.RSeq (.RCopy _ s) b) =>
      .RLetU64Zero x (.RSeq (.RScalarSetExpr x (.SVar s.locVar)) (frontNF b))
  | .RLetU64Zero x (.RSeq (.RScalarSet _ k) b) =>
      .RLetU64Zero x (.RSeq (.RScalarSet x k) (frontNF b))
  | .RLetU64Zero x (.RSeq (.RScalarSetExpr _ se) b) =>
      .RLetU64Zero x (.RSeq (.RScalarSetExpr x se) (frontNF b))
  | .RIfNz v t e => .RIfNz v (frontNF t) (frontNF e)
  | .RWhileNz v b => .RWhileNz v (frontNF b)
  | .RFor x n b => .RFor x n (frontNF b)
  | .RForRuntime x bound b => .RForRuntime x bound (frontNF b)
  | c => c

end CatCrypt.Crypto.Hax
