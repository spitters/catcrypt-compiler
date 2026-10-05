/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.TExpr
public import HaxLean.AST

/-!
# Type parameters of typed literals of class-generic definitions

`haxpipeT --emit-classes` extracts a Rust function generic in a trait bound as a Lean
definition over a class instance, and its body as an `ImpExpr` literal whose class-method
calls are builtin calls by method name. The methods of an instance, under an encoding of
its carrier, form a builtin table `Table.toBuiltins t` (`HaxAscent.Ascent.Builtins`),
with `t : Table` the list of method names and their leaves.

The typed literals carry a type parameter as `.typeVar n`. A type environment
`σ : String → Option ImpType` instantiates it (`TExpr.instTypes`); instantiation maps node
types only, so the erasure identity `f_texpr.erase = f_impExpr` of an extraction holds at
every environment.

## Main definitions

* `ImpType.substVars`, `TExpr.mapTy`, `TExpr.instTypes` — instantiation of type
  parameters in typed literals

## Main results

* `TExpr.erase_mapTy`, `TExpr.erase_instTypes` — type instantiation commutes with erasure
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.ClassBuiltins

open _root_.Hax

/-- The substitution of the type parameters of an `ImpType` by the environment `σ`; a
    parameter that `σ` does not bind is left in place. -/
def ImpType.substVars (σ : String → Option ImpType) : ImpType → ImpType
  | .tuple es => .tuple (substList σ es)
  | .option a => .option (ImpType.substVars σ a)
  | .result a b => .result (ImpType.substVars σ a) (ImpType.substVars σ b)
  | .controlFlow a b => .controlFlow (ImpType.substVars σ a) (ImpType.substVars σ b)
  | .adt n as => .adt n (substList σ as)
  | .fn ps r => .fn (substList σ ps) (ImpType.substVars σ r)
  | .ref a m => .ref (ImpType.substVars σ a) m
  | .slice a => .slice (ImpType.substVars σ a)
  | .array a n => .array (ImpType.substVars σ a) n
  | .typeVar n => (σ n).getD (.typeVar n)
  | t => t
where
  /-- `ImpType.substVars σ` on each element. -/
  substList (σ : String → Option ImpType) : List ImpType → List ImpType
    | [] => []
    | t :: ts => ImpType.substVars σ t :: substList σ ts

mutual
/-- The typed expression with every node type mapped by `g`. -/
def TExpr.mapTy (g : ImpType → ImpType) : TExpr → TExpr
  | .mk k ty => .mk (TExprKind.mapTy g k) (g ty)

/-- `TExpr.mapTy g` on every sub-expression of a kind. -/
def TExprKind.mapTy (g : ImpType → ImpType) : TExprKind → TExprKind
  | .lit v => .lit v
  | .var n => .var n
  | .letBind n v b => .letBind n (TExpr.mapTy g v) (TExpr.mapTy g b)
  | .lam ps b => .lam ps (TExpr.mapTy g b)
  | .app f as => .app f (TExpr.mapTyList g as)
  | .tuple es => .tuple (TExpr.mapTyList g es)
  | .proj e i => .proj (TExpr.mapTy g e) i
  | .ifThenElse c t e => .ifThenElse (TExpr.mapTy g c) (TExpr.mapTy g t) (TExpr.mapTy g e)
  | .match_ s arms => .match_ (TExpr.mapTy g s) (TExpr.mapTyArms g arms)
  | .unitVal => .unitVal
  | .seq a b => .seq (TExpr.mapTy g a) (TExpr.mapTy g b)
  | .borrow e => .borrow (TExpr.mapTy g e)
  | .deref e => .deref (TExpr.mapTy g e)
  | .assign n r => .assign n (TExpr.mapTy g r)
  | .forLoop v lo hi b => .forLoop v (TExpr.mapTy g lo) (TExpr.mapTy g hi) (TExpr.mapTy g b)
  | .forLoopRev v lo hi b =>
      .forLoopRev v (TExpr.mapTy g lo) (TExpr.mapTy g hi) (TExpr.mapTy g b)
  | .whileLoop c b => .whileLoop (TExpr.mapTy g c) (TExpr.mapTy g b)
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (TExpr.mapTy g e))
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (TExpr.mapTy g e)
  | .questionMark e => .questionMark (TExpr.mapTy g e)
  | .forFold v lo hi b => .forFold v (TExpr.mapTy g lo) (TExpr.mapTy g hi) (TExpr.mapTy g b)
  | .forFoldRev v lo hi b =>
      .forFoldRev v (TExpr.mapTy g lo) (TExpr.mapTy g hi) (TExpr.mapTy g b)
  | .whileFold c b => .whileFold (TExpr.mapTy g c) (TExpr.mapTy g b)
  | .forFoldReturn v lo hi b =>
      .forFoldReturn v (TExpr.mapTy g lo) (TExpr.mapTy g hi) (TExpr.mapTy g b)
  | .forFoldRevReturn v lo hi b =>
      .forFoldRevReturn v (TExpr.mapTy g lo) (TExpr.mapTy g hi) (TExpr.mapTy g b)
  | .whileFoldReturn c b => .whileFoldReturn (TExpr.mapTy g c) (TExpr.mapTy g b)
  | .cfBreak e => .cfBreak (TExpr.mapTy g e)
  | .cfContinue e => .cfContinue (TExpr.mapTy g e)
  | .cfBreakContinue e => .cfBreakContinue (TExpr.mapTy g e)
  | .ann e => .ann (TExpr.mapTy g e)
  | .namedProj n e => .namedProj n (TExpr.mapTy g e)

/-- `TExpr.mapTy g` on each element of a list. -/
def TExpr.mapTyList (g : ImpType → ImpType) : List TExpr → List TExpr
  | [] => []
  | e :: es => TExpr.mapTy g e :: TExpr.mapTyList g es

/-- `TExpr.mapTy g` on the body of each match arm. -/
def TExpr.mapTyArms (g : ImpType → ImpType) : List (ImpPat × TExpr) → List (ImpPat × TExpr)
  | [] => []
  | (p, e) :: rest => (p, TExpr.mapTy g e) :: TExpr.mapTyArms g rest
end

theorem TExpr.mapTyList_eq (g : ImpType → ImpType) (es : List TExpr) :
    TExpr.mapTyList g es = es.map (TExpr.mapTy g) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [TExpr.mapTyList, ih]

theorem TExpr.mapTyArms_eq (g : ImpType → ImpType) (arms : List (ImpPat × TExpr)) :
    TExpr.mapTyArms g arms = arms.map fun pe => (pe.1, TExpr.mapTy g pe.2) := by
  induction arms with
  | nil => rfl
  | cons pe arms ih => obtain ⟨p, e⟩ := pe; simp [TExpr.mapTyArms, ih]

/-- Mapping the node types of a typed expression leaves its erasure unchanged. -/
theorem TExpr.erase_mapTy (g : ImpType → ImpType) (e : TExpr) :
    (TExpr.mapTy g e).erase = e.erase := by
  induction e using TExpr.ind with
  | app ty f args ih =>
      simp only [TExpr.mapTy, TExprKind.mapTy, TExpr.erase, TExpr.eraseList_eq,
        TExpr.mapTyList_eq, List.map_map]
      congr 1
      exact List.map_congr_left fun a ha => ih a ha
  | tuple ty es ih =>
      simp only [TExpr.mapTy, TExprKind.mapTy, TExpr.erase, TExpr.eraseList_eq,
        TExpr.mapTyList_eq, List.map_map]
      congr 1
      exact List.map_congr_left fun a ha => ih a ha
  | match_ ty s arms ihs ih =>
      simp only [TExpr.mapTy, TExprKind.mapTy, TExpr.erase, TExpr.eraseArms_eq,
        TExpr.mapTyArms_eq, List.map_map, ihs]
      congr 1
      exact List.map_congr_left fun pa ha => by simp [ih pa ha]
  | _ => simp_all [TExpr.mapTy, TExprKind.mapTy, TExpr.erase]

/-- The typed literal of a generic definition at the type environment `σ`: each type
    parameter `.typeVar n` that `σ` binds is replaced by `σ n`. -/
def TExpr.instTypes (σ : String → Option ImpType) (e : TExpr) : TExpr :=
  TExpr.mapTy (ImpType.substVars σ) e

theorem TExpr.erase_instTypes (σ : String → Option ImpType) (e : TExpr) :
    (TExpr.instTypes σ e).erase = e.erase :=
  TExpr.erase_mapTy _ e

end CatCrypt.Hax.ClassBuiltins
