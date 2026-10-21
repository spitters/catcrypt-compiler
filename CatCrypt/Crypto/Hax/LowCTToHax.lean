/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTExit -- deprecated_module: ignore

/-!
# Translation `LowCT → Option ImpExpr` into the hax AST

`lowCTToImp c` is a hax-lean `ImpExpr` that the front `haxToLowCT` lowers back
to `c`, up to the located types the front assigns (`frontNF`).  Each arm is the
inverse image of one arm of `haxToLowCT`, in the operator vocabulary that arm
parses:

| `LowCT` | `ImpExpr` | front arm |
|---|---|---|
| `RSkip` | `unitVal` | `unitVal` |
| `RSeq a b` | `seq a b` | `seq` |
| `RSeq (RArrStore arr i src) b` | `let arr = array_update(arr, i, src); b` | `letBind` of `array_update` |
| `RScalarSet x k` | `x = k` | `assign` of an `int` literal |
| `RCall f d args` | `d = f(args)` | `assign` of a call |
| `RLetZero x t (RSeq (RCall f d args) b)` | `let x = f(args); b` | `letBind` of a call |
| `RLetZero x t (RSeq (RArrLoad d s i) b)` | `let x = index(s, i); b` | `letBind` of `index` |
| `RLetZero x t (RSeq (RTupleLoad d s i) b)` | `let x = s.i; b` | `letBind` of a projection |
| `RLetZero x t (RLetZero y u (RSeq (RCallSwap f d e args) b))` | `match f(args) { (x, y) => b }` | `match_` |
| `RLetU64Zero x (RSeq (RScalarSet x k) b)` | `let x = k; b` | `letBind` of an `int` literal |
| `RLetU64Zero x (RSeq (RScalarSetExpr x e) b)` | `let x = scalar#Op(a, b); b` | `letBind` of a scalar call |
| `RLetU64Zero x (RSeq (RScalarSetExpr x (SLimb v i)) b)` | `let x = index(v, i); b` with `i` a literal | `letBind` of a limb read |
| `RLetU64Zero x (RSeq (RScalarSetExpr x (SVar s)) b)`, `s ≠ x` | `let x = s; b` | `letBind` of a variable |
| `RLetZero x t (RSeq (RCopy d s) b)`, `d` named `x`, `s` not | `let x = s; b` | `letBind` of a variable |
| `RIfNz v t e` | `if v { t } else { e }` | `ifThenElse (var _)` |
| `RWhileNz v b` | `while v { b }` | `whileLoop (var _)` |
| `RFor x n b` | `forFold x 0 n b` | `forFold` with literal bounds |
| `RForRuntime x e b` | `forFold x 0 e b` | `forFold` with a converted bound |

A call argument is the variable of its slot.  The scalar expression of a
`scalar#Op` binding is one of the shapes `scalarCallSExpr` produces on two
variables (`scalarCallOfSExpr`), for `Op` one of `Add`, `Sub`, `Mul`, `BitAnd`,
`BitXor`, `Shr`, `Shl` and the six comparisons; a limb read is `SLimb v i` itself
(`limbReadOfSExpr`, the inverse of `limbReadArgs`), and a runtime loop bound is a variable, a
literal, or `Add`/`Sub`/`Mul` over those (`sexprToImpBound`, the inverse of
`impBoundToSExpr`); a bound that is a literal at the root is refused, since the
front reads `forFold x 0 n` with a literal `n` as `RFor`.

Every other command maps to `none`.  No arm of `haxToLowCT` produces
`RCloneCall`, `RLimbStore`, `RLimbStoreExpr`, `RCallN`, `RSelect`, `RAssert`,
`RBlock`, `RFnDef`, `RFnCall`, `RArrStoreLit`, `RArrLoadLit` or
`RCallDstThreaded`, nor an `RLetZero` or `RLetU64Zero` whose body does not open
with the command the binding computes, nor a stand-alone `RArrStore`,
`RArrLoad`, `RTupleLoad`, `RCallSwap`, `RScalarSetExpr` or `RCopy`.

The copy binding `let x = s; b` has two images.  `haxToLowCT`, which carries no
slot types, lowers it to the scalar copy `RLetU64Zero x (RSeq (RScalarSetExpr x
(SVar s)) _)`, so `frontNF` maps the whole-slot copy `RCopy` to that scalar copy
and the round trip holds with it.  The typed front `haxToLowCTEnv`, with `s`
bound at a tower type `t` other than `.TU64`, lowers it to the whole-slot copy
`RLetZero x t (RSeq (RCopy x s) _)` (`lowCTToImp_copy_haxToLowCTEnv`).  The front's
offset-start and reverse loop arms, whose bodies open with a counter shift
`RScalarSetExpr`, and its `uintLit`, `bool`, alias and `whileFold` arms, are
alternative preimages that `lowCTToImp` does not produce.

`frontNF c` is `c` with the located types the front assigns: the destination and
arguments of a call `f` at `towerOfCallName f`, array stores at `.TBytes 0`,
array and tuple loads at `.TFp`, the destination of a fused binding named
by the binder, and a copy binding as the scalar copy.

## Main definitions

* `lowCTToImp` — the translation.
* `frontNF` — the located types of the front's lowering.
* `sexprToImpBound`, `scalarCallOfSExpr`, `limbReadOfSExpr` — the scalar-expression arms.

## Main results

* `lowCTToImp_roundTrip` — `haxToLowCT e = some (frontNF c)` for every
  translation `lowCTToImp c = some e`.
* `lowCTToImp_roundTrip_of_frontNF` — `haxToLowCT e = some c` when `c` already
  carries the front's located types.
* `lowCTToImp_anfShaped` — every translation is in the front's subset
  `AnfShaped`.
* `lowCTToImp_haxToLowCTK` — the exit-flag front `haxToLowCTK false false none`
  lowers a translation to `frontNF c` with no exit.
* `lowCTToImp_copy_haxToLowCTEnv` — the typed front lowers the translation of a
  whole-slot copy back to the copy.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpPat)
open CatCrypt.Crypto.Jasmin.LowCT (TowerType LowCT Located SExpr)

/-! ## §1  Scalar expressions -/

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

/-- The front reads the call `index` on a variable and the literal of a limb as
    the limb read. -/
theorem limbReadArgs_index (v : String) (i : Nat) :
    limbReadArgs "index" [.var v, .lit (.int i)] = some (v, i) := by
  simp [limbReadArgs]

/-! ## §2  The translation -/

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

/-! ## §3  The argument and scalar-expression arms -/

/-- The front reads the call arguments of a list of slots back as the slots at
    the call's located type. -/
theorem haxArgsToLocated_locArgsToImp (dt : TowerType) (args : List Located) :
    haxArgsToLocated dt (locArgsToImp args) = some (retypeArgs dt args) := by
  induction args with
  | nil => rfl
  | cons a as ih =>
    simp only [locArgsToImp, retypeArgs, List.map_cons] at ih ⊢
    simp only [haxArgsToLocated, haxArgToLocated, ih]

/-- `impBoundToSExpr` is a left inverse of `sexprToImpBound`. -/
theorem impBoundToSExpr_sexprToImpBound (se : SExpr) (hi : ImpExpr)
    (h : sexprToImpBound se = some hi) : impBoundToSExpr hi = some se := by
  induction se generalizing hi with
  | SVar x =>
    simp only [sexprToImpBound, Option.some.injEq] at h
    subst h; rfl
  | SLit n =>
    simp only [sexprToImpBound, Option.some.injEq] at h
    subst h; simp [impBoundToSExpr]
  | SAdd a b iha ihb =>
    simp only [sexprToImpBound] at h
    cases ha : sexprToImpBound a <;> cases hb : sexprToImpBound b <;> simp only [ha, hb,
      reduceCtorEq, Option.some.injEq] at h
    subst h; simp [impBoundToSExpr, iha _ ha, ihb _ hb]
  | SSub a b iha ihb =>
    simp only [sexprToImpBound] at h
    cases ha : sexprToImpBound a <;> cases hb : sexprToImpBound b <;> simp only [ha, hb,
      reduceCtorEq, Option.some.injEq] at h
    subst h; simp [impBoundToSExpr, iha _ ha, ihb _ hb]
  | SMul a b iha ihb =>
    simp only [sexprToImpBound] at h
    cases ha : sexprToImpBound a <;> cases hb : sexprToImpBound b <;> simp only [ha, hb,
      reduceCtorEq, Option.some.injEq] at h
    subst h; simp [impBoundToSExpr, iha _ ha, ihb _ hb]
  | _ => simp [sexprToImpBound] at h

/-- A translated loop bound is a variable or a call, unless the expression is a
    literal. -/
theorem sexprToImpBound_cases (se : SExpr) (hi : ImpExpr) (h : sexprToImpBound se = some hi) :
    (∃ x, hi = .var x) ∨ (∃ n, se = .SLit n) ∨ ∃ op args, hi = .app op args := by
  cases se with
  | SVar x => simp only [sexprToImpBound, Option.some.injEq] at h; exact .inl ⟨x, h.symm⟩
  | SLit n => exact .inr (.inl ⟨n, rfl⟩)
  | SAdd a b =>
    simp only [sexprToImpBound] at h
    split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h
    exact .inr (.inr ⟨_, _, h.symm⟩)
  | SSub a b =>
    simp only [sexprToImpBound] at h
    split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h
    exact .inr (.inr ⟨_, _, h.symm⟩)
  | SMul a b =>
    simp only [sexprToImpBound] at h
    split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h
    exact .inr (.inr ⟨_, _, h.symm⟩)
  | _ => simp [sexprToImpBound] at h

/-- The scalar call read off an expression is a call computed in the scalar heap
    whose scalar expression on its two operands is that expression. -/
theorem scalarCallOfSExpr_spec (se : SExpr) (f a b : String)
    (h : scalarCallOfSExpr se = some (f, a, b)) :
    scalarCallName f = true ∧ scalarCallSExpr f (.SVar a) (.SVar b) = some se := by
  unfold scalarCallOfSExpr at h
  split at h
  all_goals first
    | (simp only [reduceCtorEq] at h)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       exact ⟨by simp [scalarCallName, scalarCallNames], by simp [scalarCallSExpr]⟩)
    | (split at h
       · rename_i hc
         obtain ⟨rfl, rfl⟩ := hc
         simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl, rfl⟩ := h
         exact ⟨by simp [scalarCallName, scalarCallNames], by simp [scalarCallSExpr]⟩
       · simp only [reduceCtorEq] at h)

/-- The call names computed in the scalar heap are neither `array_update` nor
    `index`. -/
theorem scalarCallName_ne {f : String} (h : scalarCallName f = true) :
    f ≠ "array_update" ∧ f ≠ "index" := by
  constructor <;> (rintro rfl; simp [scalarCallName, scalarCallNames] at h)

/-! ## §4  The round trip -/

/-- **Round trip.**  The front lowers the translation of a command to the
    command with the front's located types. -/
theorem lowCTToImp_roundTrip (c : LowCT) (e : ImpExpr) (h : lowCTToImp c = some e) :
    haxToLowCT e = some (frontNF c) := by
  induction c using lowCTToImp.induct generalizing e
  case case1 =>
    simp only [lowCTToImp, Option.some.injEq] at h
    subst h
    simp [haxToLowCT, frontNF]
  case case2 arr idx src b ih =>
    simp only [lowCTToImp] at h
    cases hb : lowCTToImp b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      simp [haxToLowCT, haxArgsToLocated, haxArgToLocated, ih b' hb, frontNF]
  case case3 a b hna a' b' hb ha iha ihb =>
    rw [lowCTToImp.eq_3 _ _ hna, ha, hb] at h
    simp only [Option.some.injEq] at h
    subst h
    rw [frontNF.eq_3 _ _ hna]
    simp [haxToLowCT, iha a' ha, ihb b' hb]
  case case4 a b hna hnone _ _ =>
    rw [lowCTToImp.eq_3 _ _ hna] at h
    cases ha : lowCTToImp a <;> cases hb : lowCTToImp b <;> simp only [ha, hb, reduceCtorEq] at h
    exact (hnone _ _ ha hb).elim
  case case5 x k =>
    simp only [lowCTToImp, Option.some.injEq] at h
    subst h
    simp [haxToLowCT, frontNF]
  case case6 f d args =>
    simp only [lowCTToImp, callToImp] at h
    split at h
    · cases h
    · rename_i hf
      simp only [Option.some.injEq] at h
      subst h
      simp only [haxToLowCT, haxArgsToLocated_locArgsToImp, frontNF]
      split
      · rename_i hfa
        rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩ <;>
          simp [locArgsToImp, hfa] at hf ⊢
      · rfl
  case case7 x t f d args b hc ih =>
    simp only [lowCTToImp, if_pos hc] at h
    cases hb : lowCTToImp b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨_, h1, h2, h3⟩ := hc
      simp [haxToLowCT, haxArgsToLocated_locArgsToImp, ih b' hb, frontNF, h1, h2, h3]
  case case9 t d s idx b ih =>
    simp only [lowCTToImp, ↓reduceIte] at h
    cases hb : lowCTToImp b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      simp [haxToLowCT, haxArgsToLocated, haxArgToLocated, ih b' hb, frontNF]
  case case11 t d s i b ih =>
    simp only [lowCTToImp, ↓reduceIte] at h
    cases hb : lowCTToImp b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      simp [haxToLowCT, ih b' hb, frontNF]
  case case13 x t y u f d el args b hc ih =>
    simp only [lowCTToImp, if_pos hc] at h
    cases hb : lowCTToImp b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := hc
      simp [haxToLowCT, haxArgsToLocated_locArgsToImp, ih b' hb, frontNF]
  case case15 y k b ih =>
    simp only [lowCTToImp, ↓reduceIte] at h
    cases hb : lowCTToImp b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      simp [haxToLowCT, ih b' hb, frontNF]
  case case17 y se b f a a2 hsc ih =>
    simp only [lowCTToImp, hsc, ↓reduceIte] at h
    cases hb : lowCTToImp b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨hn, hse⟩ := scalarCallOfSExpr_spec se f a a2 hsc
      obtain ⟨h1, h2⟩ := scalarCallName_ne hn
      simp [haxToLowCT, haxArgsToLocated, haxArgToLocated, ih b' hb, frontNF, h1, h2, hn, hse]
  case case19 y se b hsc v i hlr ih =>
    simp only [lowCTToImp, hsc, hlr, ↓reduceIte] at h
    cases hb : lowCTToImp b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      obtain rfl : se = .SLimb v i := by
        cases se <;> simp_all [limbReadOfSExpr]
      simp [haxToLowCT, haxArgsToLocated, haxArgToLocated, limbReadArgs_index, ih b' hb, frontNF]
  case case21 y b s hc _ _ ih =>
    obtain ⟨rfl, hs⟩ := hc
    simp only [lowCTToImp, scalarCallOfSExpr, limbReadOfSExpr, hs, ne_eq, not_false_eq_true,
      and_self, ↓reduceIte] at h
    cases hb : lowCTToImp b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      rw [haxToLowCT_letBind_var_ne _ _ _ (Ne.symm hs), ih b' hb]
      simp [frontNF]
  case case24 v t el t' el' hel ht iht ihel =>
    simp only [lowCTToImp, ht, hel, Option.some.injEq] at h
    subst h
    simp [haxToLowCT, iht t' ht, ihel el' hel, frontNF]
  case case25 =>
    simp only [lowCTToImp, reduceCtorEq] at h
  case case26 v b ih =>
    simp only [lowCTToImp] at h
    cases hb : lowCTToImp b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      simp [haxToLowCT, ih b' hb, frontNF]
  case case27 x n b ih =>
    simp only [lowCTToImp] at h
    cases hb : lowCTToImp b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      simp [haxToLowCT, ih b' hb, frontNF]
  case case29 x bound b hi b' hb hbd hnl ih =>
    have hL : lowCTToImp (.RForRuntime x bound b) = some (.forFold x (.lit (.int 0)) hi b') := by
      cases bound <;> first | exact absurd rfl (hnl _) | simp [lowCTToImp, hbd, hb]
    rw [hL, Option.some.injEq] at h
    subst h
    have hI := impBoundToSExpr_sexprToImpBound bound hi hbd
    have hF : frontNF (.RForRuntime x bound b) = .RForRuntime x bound (frontNF b) := by
      simp [frontNF]
    rw [hF]
    rcases sexprToImpBound_cases bound hi hbd with ⟨v, rfl⟩ | ⟨n, rfl⟩ | ⟨op, args, rfl⟩
    · simp [haxToLowCT, hI, ih b' hb]
    · exact absurd rfl (hnl n)
    · simp [haxToLowCT, hI, ih b' hb]
  case case30 x bound b hnl hnone _ =>
    have hL : lowCTToImp (.RForRuntime x bound b) =
        match sexprToImpBound bound, lowCTToImp b with
        | some hi, some b' => some (.forFold x (.lit (.int 0)) hi b')
        | _, _ => none := by
      cases bound <;> first | exact absurd rfl (hnl _) | simp [lowCTToImp]
    rw [hL] at h
    cases h1 : sexprToImpBound bound <;> cases h2 : lowCTToImp b <;>
      simp only [h1, h2, reduceCtorEq] at h
    exact (hnone _ _ h1 h2).elim
  case case31 x t d s b hc ih =>
    simp only [lowCTToImp, if_pos hc] at h
    cases hb : lowCTToImp b with
    | none => simp [hb] at h
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      rw [haxToLowCT_letBind_var_ne _ _ _ (Ne.symm hc.2), ih b' hb]
      simp [frontNF]
  case case33 =>
    rw [lowCTToImp.eq_19] at h
    · simp only [reduceCtorEq] at h
    all_goals assumption
  all_goals simp [lowCTToImp, *] at h

/-- On a command whose located types are those of the front's lowering, the
    round trip is the identity. -/
theorem lowCTToImp_roundTrip_of_frontNF (c : LowCT) (e : ImpExpr) (h : lowCTToImp c = some e)
    (hNF : frontNF c = c) : haxToLowCT e = some c := by
  rw [lowCTToImp_roundTrip c e h, hNF]

/-- Every translation is in the front's subset `AnfShaped`. -/
theorem lowCTToImp_anfShaped (c : LowCT) (e : ImpExpr) (h : lowCTToImp c = some e) :
    AnfShaped e = true := by
  rw [← haxToLowCT_isSome_iff_anf, lowCTToImp_roundTrip c e h]
  rfl

/-- The exit-flag front `haxToLowCTK` without scalar-operation arms, outside tail
    position and outside every loop, lowers a translation to `frontNF c` with no
    exit. -/
theorem lowCTToImp_haxToLowCTK (c : LowCT) (e : ImpExpr) (h : lowCTToImp c = some e) :
    haxToLowCTK false false none e = some (frontNF c, false) := by
  have hK := lowCTToImp_roundTrip c e h
  rw [haxToLowCT_eq_haxToLowCTK_none] at hK
  rcases hk : haxToLowCTK false false none e with _ | ⟨c', _ | _⟩ <;>
    simp only [hk, exitFree, reduceCtorEq, Option.some.injEq] at hK
  rw [hK]

/-- A command that `lowCTToImp` translates lands in the front's subset: its
    translation is `AnfShaped` and the front lowers it to `frontNF c`. -/
theorem lowCTToImp_inFront_of_isSome (c : LowCT) (h : (lowCTToImp c).isSome = true) :
    ∃ e, lowCTToImp c = some e ∧ haxToLowCT e = some (frontNF c) ∧ AnfShaped e = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h
  exact ⟨e, he, lowCTToImp_roundTrip c e he, lowCTToImp_anfShaped c e he⟩

/-! ## §5  The copy under the typed front -/

/-- **The copy under the typed front.**  A whole-slot copy of `s` into the fresh
    slot `x` at a tower type `t` other than `.TU64` translates to
    `let x = s; b'`, and the typed front `haxToLowCTEnv`, with `s` bound at `t`
    in its type environment, lowers that binding back to the copy, followed by
    its lowering of `b'` with `x` bound at `t`. -/
theorem lowCTToImp_copy_haxToLowCTEnv (env : TypeEnv) (leaves : LeafTable) (x s : String)
    (t : TowerType) (b bC : LowCT) (b' : ImpExpr) (hb : lowCTToImp b = some b')
    (hxs : x ≠ s) (hz : mlkemZeroConst? s = none) (hs : env.findOpt s = some t)
    (ht : t ≠ .TU64) (hbody : haxToLowCTEnv ((x, t) :: env) leaves b' = some bC) :
    lowCTToImp (.RLetZero x t (.RSeq (.RCopy { locVar := x, locSrc := t }
        { locVar := s, locSrc := t }) b)) = some (.letBind x (.var s) b') ∧
      haxToLowCTEnv env leaves (.letBind x (.var s) b') =
        some (.RLetZero x t (.RSeq (.RCopy { locVar := x, locSrc := t }
          { locVar := s, locSrc := t }) bC)) := by
  refine ⟨?_, ?_⟩
  · simp [lowCTToImp, hb, Ne.symm hxs]
  · cases t <;> simp_all [haxToLowCTEnv]

end CatCrypt.Crypto.Hax
