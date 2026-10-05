/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
public import CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck

/-!
# The leakage model of a coproduct of dialects

For leakage models `M` of `d` and `N` of `e`, `sumLeak M N` is the leakage model of the
coproduct `Dialect.sum d e`: an operation has the event class of its summand, and a value
is read by the reading of its summand. The events of an operation of the coproduct are the
events of the operation in its summand on the arguments with the tags stripped
(`opLeak_inl`, `opLeak_inr`), so a program included by `inlLowering` or `inrLowering`
emits, from the included valuation, the events it emits in its summand (`ctLeak_inl`,
`ctLeak_inr`).

The level checker `ComLevelCheck.Com.levelCheck` and its soundness are stated for every
dialect with a leakage model, so they hold at `sumLeak M N` (`sumLeak_levelCheck_sound`).
The checker accepts an included program at the included labels exactly when it accepts the
program in its summand (`levelCheck_inl`, `levelCheck_inr`).

## Main definitions

* `sumValNat`, `sumLeak` — the reading of values and the leakage model of the coproduct.
* `mapLabelsInl`, `mapLabelsInr` — labels of a context as labels of the included context.

## Main results

* `sumLeak_kind_inl`, `sumLeak_kind_inr` — the event class of an injected operation.
* `opLeak_inl`, `opLeak_inr` — the events of an injected operation.
* `ctLeak_inl`, `ctLeak_inr` — an included program emits the events of its source.
* `levelCheck_inl`, `levelCheck_inr` — inclusion keeps the result of the level checker.
* `sumLeak_levelCheck_sound` — a program of the coproduct the checker accepts is constant
  time.
* `comCT_inl`, `comCT_inr` — an included program the checker accepts in its summand is
  constant time in the coproduct.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)
open Ctxt (Var Valuation)

variable {d e : Dialect} [TyDenote d.Ty] [TyDenote e.Ty] [DialectSignature d]
  [DialectSignature e]

/-! ## 1. The model -/

/-- The reading of a value of the coproduct: the reading of its summand. -/
def sumValNat (M : LeakModel d) (N : LeakModel e) : (t : (Dialect.sum d e).Ty) → ⟦t⟧ → Nat
  | .inl t, x => M.valNat t x
  | .inr t, x => N.valNat t x

/-- **The leakage model of the coproduct**: an operation has the event class of its
    summand, and a value the reading of its summand. -/
def sumLeak (M : LeakModel d) (N : LeakModel e) : LeakModel (Dialect.sum d e) where
  kind := Sum.elim M.kind N.kind
  valNat := sumValNat M N

/-- The event class of a left operation is its class in the left summand. -/
@[simp] theorem sumLeak_kind_inl (M : LeakModel d) (N : LeakModel e) (op : d.Op) :
    (sumLeak M N).kind (.inl op) = M.kind op := rfl

/-- The event class of a right operation is its class in the right summand. -/
@[simp] theorem sumLeak_kind_inr (M : LeakModel d) (N : LeakModel e) (op : e.Op) :
    (sumLeak M N).kind (.inr op) = N.kind op := rfl

/-- The reading of a left value is its reading in the left summand. -/
@[simp] theorem sumLeak_valNat_inl (M : LeakModel d) (N : LeakModel e) (t : d.Ty) (x : ⟦t⟧) :
    (sumLeak M N).valNat (.inl t) x = M.valNat t x := rfl

/-- The reading of a right value is its reading in the right summand. -/
@[simp] theorem sumLeak_valNat_inr (M : LeakModel d) (N : LeakModel e) (t : e.Ty) (x : ⟦t⟧) :
    (sumLeak M N).valNat (.inr t) x = N.valNat t x := rfl

/-! ## 2. The events of an injected operation -/

/-- The readings of left values are their readings in the left summand. -/
theorem valsNat_unmapInl (M : LeakModel d) (N : LeakModel e) :
    ∀ {ts : List d.Ty} (vals : HVector (fun t => ⟦t⟧) (ts.map (Sum.inl (β := e.Ty)))),
      valsNat (sumLeak M N) vals = valsNat M (unmapInl vals)
  | [], .nil => rfl
  | _ :: _, .cons x xs => by
      show M.valNat _ x :: valsNat (sumLeak M N) xs = M.valNat _ x :: valsNat M (unmapInl xs)
      rw [valsNat_unmapInl M N xs]

/-- The readings of right values are their readings in the right summand. -/
theorem valsNat_unmapInr (M : LeakModel d) (N : LeakModel e) :
    ∀ {ts : List e.Ty} (vals : HVector (fun t => ⟦t⟧) (ts.map (Sum.inr (α := d.Ty)))),
      valsNat (sumLeak M N) vals = valsNat N (unmapInr vals)
  | [], .nil => rfl
  | _ :: _, .cons x xs => by
      show N.valNat _ x :: valsNat (sumLeak M N) xs = N.valNat _ x :: valsNat N (unmapInr xs)
      rw [valsNat_unmapInr M N xs]

/-- **The events of a left operation** are its events in the left summand on the arguments
    with the tags stripped. -/
theorem opLeak_inl (M : LeakModel d) (N : LeakModel e) (op : d.Op)
    (vals : HVector (fun t => ⟦t⟧) ((DialectSignature.sig op).map (Sum.inl (β := e.Ty)))) :
    opLeak (sumLeak M N) (.inl op) vals = opLeak M op (unmapInl vals) := by
  unfold opLeak
  rw [sumLeak_kind_inl, valsNat_unmapInl M N vals]

/-- **The events of a right operation** are its events in the right summand on the
    arguments with the tags stripped. -/
theorem opLeak_inr (M : LeakModel d) (N : LeakModel e) (op : e.Op)
    (vals : HVector (fun t => ⟦t⟧) ((DialectSignature.sig op).map (Sum.inr (α := d.Ty)))) :
    opLeak (sumLeak M N) (.inr op) vals = opLeak N op (unmapInr vals) := by
  unfold opLeak
  rw [sumLeak_kind_inr, valsNat_unmapInr M N vals]

/-- A right operation of a quiet class emits no event. -/
theorem opLeak_inr_quiet (M : LeakModel d) (N : LeakModel e) (op : e.Op)
    (h : N.kind op = .quiet)
    (vals : HVector (fun t => ⟦t⟧) ((DialectSignature.sig op).map (Sum.inr (α := d.Ty)))) :
    opLeak (sumLeak M N) (.inr op) vals = [] := by
  unfold opLeak
  rw [sumLeak_kind_inr, h]

/-! ## 3. The events of an included program -/

section Programs

variable [DialectDenote d] [DialectDenote e]

/-- **Leakage along the left inclusion.** A program of `d` included into the coproduct
    emits, from the included valuation and at the model `sumLeak M N`, the events it emits
    at `M`. -/
theorem ctLeak_inl (M : LeakModel d) (N : LeakModel e) {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) :
    ∀ V : Valuation Γ, Com.ctLeak (sumLeak M N) ((inlLowering d e).lowerCom c)
      (mapValInl (e := e) V) = Com.ctLeak M c V := by
  induction c with
  | ret v => intro V; rfl
  | var ex body ih =>
      intro V
      obtain ⟨op, hop, args⟩ := ex
      subst hop
      show opLeak (sumLeak M N) (.inl op)
          (Expr.lookupArgs (mapArgsInl (e := e) args) (mapValInl V)) ++
          Com.ctLeak (sumLeak M N) ((inlLowering d e).lowerCom body)
            (HVector.cons (DialectDenote.denote op (unmapInl
              (Expr.lookupArgs (mapArgsInl (e := e) args) (mapValInl V)))) (mapValInl V)) =
        opLeak M op (Expr.lookupArgs args V) ++ Com.ctLeak M body _
      rw [opLeak_inl, lookupArgs_mapArgsInl args V, ← ih]
      rfl

/-- **Leakage along the right inclusion.** A program of `e` included into the coproduct
    emits, from the included valuation and at the model `sumLeak M N`, the events it emits
    at `N`. -/
theorem ctLeak_inr (M : LeakModel d) (N : LeakModel e) {Γ : Ctxt e} {t : e.Ty}
    (c : Com e Γ t) :
    ∀ V : Valuation Γ, Com.ctLeak (sumLeak M N) ((inrLowering d e).lowerCom c)
      (mapValInr (d := d) V) = Com.ctLeak N c V := by
  induction c with
  | ret v => intro V; rfl
  | var ex body ih =>
      intro V
      obtain ⟨op, hop, args⟩ := ex
      subst hop
      show opLeak (sumLeak M N) (.inr op)
          (Expr.lookupArgs (mapArgsInr (d := d) args) (mapValInr V)) ++
          Com.ctLeak (sumLeak M N) ((inrLowering d e).lowerCom body)
            (HVector.cons (DialectDenote.denote op (unmapInr
              (Expr.lookupArgs (mapArgsInr (d := d) args) (mapValInr V)))) (mapValInr V)) =
        opLeak N op (Expr.lookupArgs args V) ++ Com.ctLeak N body _
      rw [opLeak_inr, lookupArgs_mapArgsInr args V, ← ih]
      rfl

end Programs

/-! ## 4. The level checker on the coproduct -/

/-- The labels of a context as labels of the left-included context. -/
def mapLabelsInl : {Γ : Ctxt d} → Labels Γ → Labels (d := Dialect.sum d e) (Γ.map Sum.inl)
  | [], _ => .nil
  | _ :: _, .cons l L => .cons l (mapLabelsInl L)

/-- The labels of a context as labels of the right-included context. -/
def mapLabelsInr : {Γ : Ctxt e} → Labels Γ → Labels (d := Dialect.sum d e) (Γ.map Sum.inr)
  | [], _ => .nil
  | _ :: _, .cons l L => .cons l (mapLabelsInr L)

omit [TyDenote d.Ty] [TyDenote e.Ty] [DialectSignature d] [DialectSignature e] in
/-- The level of a left-included variable is the level of the variable. -/
theorem lvlOf_mapVarInl : ∀ {Γ : Ctxt d} {t : d.Ty} (v : Var Γ t) (L : Labels Γ),
    lvlOf (mapVarInl (e := e) v) (mapLabelsInl L) = lvlOf v L
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ L => lvlOf_mapVarInl v L

omit [TyDenote d.Ty] [TyDenote e.Ty] [DialectSignature d] [DialectSignature e] in
/-- The level of a right-included variable is the level of the variable. -/
theorem lvlOf_mapVarInr : ∀ {Γ : Ctxt e} {t : e.Ty} (v : Var Γ t) (L : Labels Γ),
    lvlOf (mapVarInr (d := d) v) (mapLabelsInr L) = lvlOf v L
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ L => lvlOf_mapVarInr v L

omit [TyDenote d.Ty] [TyDenote e.Ty] [DialectSignature d] [DialectSignature e] in
/-- The levels of left-included arguments are the levels of the arguments. -/
theorem argLvls_mapArgsInl {Γ : Ctxt d} (L : Labels Γ) :
    ∀ {ts : List d.Ty} (args : HVector (fun t => Var Γ t) ts),
      argLvls (mapLabelsInl (e := e) L) (mapArgsInl (e := e) args) = argLvls L args
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      show lvlOf _ _ :: argLvls _ _ = lvlOf v L :: argLvls L vs
      rw [lvlOf_mapVarInl v L, argLvls_mapArgsInl L vs]

omit [TyDenote d.Ty] [TyDenote e.Ty] [DialectSignature d] [DialectSignature e] in
/-- The levels of right-included arguments are the levels of the arguments. -/
theorem argLvls_mapArgsInr {Γ : Ctxt e} (L : Labels Γ) :
    ∀ {ts : List e.Ty} (args : HVector (fun t => Var Γ t) ts),
      argLvls (mapLabelsInr (d := d) L) (mapArgsInr (d := d) args) = argLvls L args
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      show lvlOf _ _ :: argLvls _ _ = lvlOf v L :: argLvls L vs
      rw [lvlOf_mapVarInr v L, argLvls_mapArgsInr L vs]

/-- The constraint of a left operation is its constraint in the left summand. -/
@[simp] theorem opAccepts_inl (M : LeakModel d) (N : LeakModel e) (op : d.Op)
    (ls : List SecretLevel) : opAccepts (sumLeak M N) (.inl op) ls = opAccepts M op ls := rfl

/-- The constraint of a right operation is its constraint in the right summand. -/
@[simp] theorem opAccepts_inr (M : LeakModel d) (N : LeakModel e) (op : e.Op)
    (ls : List SecretLevel) : opAccepts (sumLeak M N) (.inr op) ls = opAccepts N op ls := rfl

section Check

variable [DialectDenote d] [DialectDenote e]

omit [DialectDenote d] [DialectDenote e] in
/-- **The left inclusion keeps the result of the level checker.** -/
theorem levelCheck_inl (M : LeakModel d) (N : LeakModel e) {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) :
    ∀ L : Labels Γ, Com.levelCheck (sumLeak M N) ((inlLowering d e).lowerCom c)
      (mapLabelsInl L) = Com.levelCheck M c L := by
  induction c with
  | ret v => intro L; rfl
  | var ex body ih =>
      intro L
      obtain ⟨op, hop, args⟩ := ex
      subst hop
      show (opAccepts (sumLeak M N) (.inl op)
            (argLvls (mapLabelsInl (e := e) L) (mapArgsInl (e := e) args)) &&
          Com.levelCheck (sumLeak M N) ((inlLowering d e).lowerCom body)
            (HVector.cons (joinAll (argLvls (mapLabelsInl (e := e) L)
              (mapArgsInl (e := e) args))) (mapLabelsInl L))) =
        (opAccepts M op (argLvls L args) &&
          Com.levelCheck M body (.cons (joinAll (argLvls L args)) L))
      rw [argLvls_mapArgsInl L args, opAccepts_inl, ← ih]
      rfl

omit [DialectDenote d] [DialectDenote e] in
/-- **The right inclusion keeps the result of the level checker.** -/
theorem levelCheck_inr (M : LeakModel d) (N : LeakModel e) {Γ : Ctxt e} {t : e.Ty}
    (c : Com e Γ t) :
    ∀ L : Labels Γ, Com.levelCheck (sumLeak M N) ((inrLowering d e).lowerCom c)
      (mapLabelsInr L) = Com.levelCheck N c L := by
  induction c with
  | ret v => intro L; rfl
  | var ex body ih =>
      intro L
      obtain ⟨op, hop, args⟩ := ex
      subst hop
      show (opAccepts (sumLeak M N) (.inr op)
            (argLvls (mapLabelsInr (d := d) L) (mapArgsInr (d := d) args)) &&
          Com.levelCheck (sumLeak M N) ((inrLowering d e).lowerCom body)
            (HVector.cons (joinAll (argLvls (mapLabelsInr (d := d) L)
              (mapArgsInr (d := d) args))) (mapLabelsInr L))) =
        (opAccepts N op (argLvls L args) &&
          Com.levelCheck N body (.cons (joinAll (argLvls L args)) L))
      rw [argLvls_mapArgsInr L args, opAccepts_inr, ← ih]
      rfl

/-- **Soundness of the level checker on the coproduct**: `levelCheck_sound` at the model
    `sumLeak M N`. -/
theorem sumLeak_levelCheck_sound (M : LeakModel d) (N : LeakModel e)
    {Γ : Ctxt (Dialect.sum d e)} {t : (Dialect.sum d e).Ty} (c : Com (Dialect.sum d e) Γ t)
    (L : Labels Γ) (h : Com.levelCheck (sumLeak M N) c L = true) : ComCT (sumLeak M N) L c :=
  levelCheck_sound (sumLeak M N) c L h

/-- A program the checker accepts in the left summand is constant time in the coproduct. -/
theorem comCT_inl (M : LeakModel d) (N : LeakModel e) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t)
    (L : Labels Γ) (h : Com.levelCheck M c L = true) :
    ComCT (sumLeak M N) (mapLabelsInl L) ((inlLowering d e).lowerCom c) :=
  sumLeak_levelCheck_sound M N _ _ ((levelCheck_inl M N c L).trans h)

/-- A program the checker accepts in the right summand is constant time in the coproduct. -/
theorem comCT_inr (M : LeakModel d) (N : LeakModel e) {Γ : Ctxt e} {t : e.Ty} (c : Com e Γ t)
    (L : Labels Γ) (h : Com.levelCheck N c L = true) :
    ComCT (sumLeak M N) (mapLabelsInr L) ((inrLowering d e).lowerCom c) :=
  sumLeak_levelCheck_sound M N _ _ ((levelCheck_inr M N c L).trans h)

end Check

end CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
