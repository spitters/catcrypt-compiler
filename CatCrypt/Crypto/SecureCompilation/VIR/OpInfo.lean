/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
public import CatCrypt.Crypto.SecureCompilation.VIR.CoreM
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum

/-!
# The operation information of a dialect

`OpTraits d` records the properties of the operations of a dialect `d` that a
generic transformation reads: which operations are pure (may be merged by value
numbering), speculatable (may be executed under a false guard), constant-like
(take no argument), and the cost of each operation. `OpInfo d` adds the leakage
model (`ComLevelCheck.LeakModel`), so that one record carries the operation
information of a dialect at one target parameter.

The record is data. The properties it claims are separate propositions, proved per
dialect: `PureLaw T M` (a pure operation's monadic denotation is the return of its
pure denotation), `SpecLaw T` (a speculatable operation's `Option` denotation is
`some` at every argument), `ConstLaw T` (a constant-like operation has the empty
signature). A predicate value `false` is always admissible.

Under the operation sum `Dialect.opSum` every field of the record is a case split
(`OpTraits.opSum`), and so are the laws; the monadic denotation of the sum is the
case split `DialectOpSum.instDialectDenoteMOpSum`. Under `Dialect.retype` the
operations are unchanged, so the record carries over as it is (`OpTraits.retype`).
A leakage model of the sum agrees with a leakage model of `d` along the inclusion
`DialectOpSum.inlVia E` when it gives the left operations the kinds of `d` and
reads transported values as `d` reads them; the leakage model of the sum
`leakSum` (`Optimizer/Rewrite/AegraphSum.lean`) is one such model.

## Main definitions

* `OpTraits`, `OpTraits.key`, `OpTraits.idle`, `OpTraits.opSum`, `OpTraits.retype`
* `OpInfo`: an `OpTraits` record together with a leakage model
* `PureLaw`, `SpecLaw`, `ConstLaw`
* `DialectOpSum.instDialectDenoteMOpSum`: the monadic denotation of an operation sum

## Main results

* `ComLevelCheck.Expr.ctLeak_of_quiet`: an expression whose operation is quiet emits
  no event, for every dialect and leakage model
* `ComLevelCheck.Expr.ctLeak_indep_of_nullary`: the events of an expression whose
  operation takes no argument do not depend on the valuation
* `ConstLaw.ctLeak_indep`: the same for a constant-like operation of a lawful record
* `ConstLaw.opSum`, `SpecLaw.opSum`, `PureLaw.opSum`: the laws of two dialects give
  the laws of their operation sum
* `ConstLaw.idle`, `SpecLaw.idle`, `PureLaw.idle`, `ConstLaw.retype`
* `DialectOpSum.ctLeak_inlVia`: the events of a program included along a type
  embedding are its events in the source dialect
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

universe u v

open Ctxt (Var Valuation)
open ComLevelCheck (LeakKind LeakModel valsNat opLeak)

/-! ## 1. The record -/

/-- The operation properties of a dialect read by generic transformations. -/
structure OpTraits (d : Dialect.{u, v}) where
  /-- The operation may be merged with an equal operation on equal arguments. -/
  pure : d.Op → Bool
  /-- The operation may be executed whatever the guard of its use. -/
  speculatable : d.Op → Bool
  /-- The operation takes no argument. -/
  constLike : d.Op → Bool
  /-- The cost of the operation. -/
  cost : d.Op → Nat

namespace OpTraits

variable {d e : Dialect.{u, v}}

/-- The extraction weight of an operation: twice its cost, plus one unless the
    operation is constant-like. -/
def key (T : OpTraits d) (op : d.Op) : Nat :=
  2 * T.cost op + if T.constLike op then 0 else 1

/-- The record that marks no operation pure, speculatable or constant-like, at cost
    one. -/
def idle (d : Dialect.{u, v}) : OpTraits d where
  pure _ := false
  speculatable _ := false
  constLike _ := false
  cost _ := 1

/-- The record of an operation sum: every field is the case split over the tag. -/
def opSum (T₁ : OpTraits d) (T₂ : OpTraits e) : OpTraits (d.opSum e) where
  pure := Sum.elim T₁.pure T₂.pure
  speculatable := Sum.elim T₁.speculatable T₂.speculatable
  constLike := Sum.elim T₁.constLike T₂.constLike
  cost := Sum.elim T₁.cost T₂.cost

/-- The record of a re-typed dialect: the operations are unchanged, so the record is
    the same. -/
def retype (T : OpTraits d) (τ : Type v) : OpTraits (d.retype τ) :=
  ⟨T.pure, T.speculatable, T.constLike, T.cost⟩

@[simp] theorem key_opSum_inl (T₁ : OpTraits d) (T₂ : OpTraits e) (op : d.Op) :
    (T₁.opSum T₂).key (.inl op) = T₁.key op := rfl

@[simp] theorem key_opSum_inr (T₁ : OpTraits d) (T₂ : OpTraits e) (op : e.Op) :
    (T₁.opSum T₂).key (.inr op) = T₂.key op := rfl

end OpTraits

/-- The operation information of a dialect: the operation properties together with
    the leakage model. -/
structure OpInfo (d : Dialect.{u, v}) [TyDenote d.Ty] [DialectSignature d]
    extends OpTraits d, LeakModel d

/-! ## 2. The laws -/

section Laws

variable {d : Dialect.{u, v}} [TyDenote d.Ty] [DialectSignature d]

/-- A pure operation's denotation in the monad `M` is the return of its pure
    denotation. -/
def PureLaw (T : OpTraits d) (M : Type → Type) [Monad M] [DialectDenote d]
    [DialectDenoteM d M] : Prop :=
  ∀ op, T.pure op = true → ∀ args : HVector (fun t => ⟦t⟧) (DialectSignature.sig op),
    DialectDenoteM.denoteM (M := M) op args = pure (DialectDenote.denote op args)

/-- A speculatable operation's `Option` denotation is `some` at every argument. -/
def SpecLaw (T : OpTraits d) [DialectDenoteM d Option] : Prop :=
  ∀ op, T.speculatable op = true → ∀ args : HVector (fun t => ⟦t⟧) (DialectSignature.sig op),
    (DialectDenoteM.denoteM (M := Option) op args).isSome = true

omit [TyDenote d.Ty] in
/-- A constant-like operation has the empty signature. -/
def ConstLaw (T : OpTraits d) : Prop :=
  ∀ op, T.constLike op = true → DialectSignature.sig op = []

theorem PureLaw.idle (M : Type → Type) [Monad M] [DialectDenote d] [DialectDenoteM d M] :
    PureLaw (OpTraits.idle d) M := fun _ h => nomatch h

theorem SpecLaw.idle [DialectDenoteM d Option] : SpecLaw (OpTraits.idle d) :=
  fun _ h => nomatch h

omit [TyDenote d.Ty] in
theorem ConstLaw.idle : ConstLaw (OpTraits.idle d) := fun _ h => nomatch h

end Laws

/-! ## 3. Generic leakage lemmas -/

namespace ComLevelCheck

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d]

/-- An expression whose operation is quiet emits no event. -/
theorem Expr.ctLeak_of_quiet (M : LeakModel d) {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t)
    (h : M.kind e.op = .quiet) (V : Valuation Γ) : Expr.ctLeak M e V = [] := by
  unfold Expr.ctLeak opLeak
  rw [h]

/-- The readings of the values of the empty argument list are empty. -/
theorem valsNat_of_eq_nil (M : LeakModel d) :
    ∀ {tys : List d.Ty}, tys = [] → ∀ vals : HVector (fun t => ⟦t⟧) tys, valsNat M vals = []
  | [], _, .nil => rfl

/-- The events of an operation without arguments do not depend on the argument
    values. -/
theorem opLeak_eq_of_nullary (M : LeakModel d) (op : d.Op)
    (h : DialectSignature.sig op = [])
    (vals₁ vals₂ : HVector (fun t => ⟦t⟧) (DialectSignature.sig op)) :
    opLeak M op vals₁ = opLeak M op vals₂ := by
  unfold opLeak
  rw [valsNat_of_eq_nil M h vals₁, valsNat_of_eq_nil M h vals₂]

/-- The events of an expression whose operation takes no argument do not depend on
    the valuation. -/
theorem Expr.ctLeak_indep_of_nullary (M : LeakModel d) {Γ : Ctxt d} {t : d.Ty}
    (e : Expr d Γ t) (h : DialectSignature.sig e.op = []) (V₁ V₂ : Valuation Γ) :
    Expr.ctLeak M e V₁ = Expr.ctLeak M e V₂ :=
  opLeak_eq_of_nullary M e.op h _ _

end ComLevelCheck

/-- Under a lawful record, the events of an expression whose operation is
    constant-like do not depend on the valuation. -/
theorem ConstLaw.ctLeak_indep {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    {T : OpTraits d} (hT : ConstLaw T) (M : LeakModel d) {Γ : Ctxt d} {t : d.Ty}
    (e : Expr d Γ t) (h : T.constLike e.op = true) (V₁ V₂ : Valuation Γ) :
    ComLevelCheck.Expr.ctLeak M e V₁ = ComLevelCheck.Expr.ctLeak M e V₂ :=
  ComLevelCheck.Expr.ctLeak_indep_of_nullary M e (hT _ h) V₁ V₂

/-! ## 4. Operation sums and re-typing -/

namespace DialectOpSum

variable {O₁ O₂ : Type} {T : Type} [TyDenote T]
  [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectSignature (⟨O₂, T⟩ : Dialect)]

/-- The monadic denotation of an operation sum: the summand's monadic denotation. -/
instance instDialectDenoteMOpSum {M : Type → Type}
    [DialectDenoteM (⟨O₁, T⟩ : Dialect) M] [DialectDenoteM (⟨O₂, T⟩ : Dialect) M] :
    DialectDenoteM (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) M where
  denoteM op := match op with
    | .inl o => fun args => DialectDenoteM.denoteM (d := ⟨O₁, T⟩) o args
    | .inr o => fun args => DialectDenoteM.denoteM (d := ⟨O₂, T⟩) o args

end DialectOpSum

section SumLaws

variable {O₁ O₂ : Type} {T : Type}
  [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectSignature (⟨O₂, T⟩ : Dialect)]

/-- The constant laws of two dialects give the constant law of their operation sum. -/
theorem ConstLaw.opSum {T₁ : OpTraits ⟨O₁, T⟩} {T₂ : OpTraits ⟨O₂, T⟩}
    (h₁ : ConstLaw T₁) (h₂ : ConstLaw T₂) : ConstLaw (T₁.opSum T₂)
  | .inl o, h => h₁ o h
  | .inr o, h => h₂ o h

variable [TyDenote T]

/-- The speculation laws of two dialects give the speculation law of their operation
    sum. -/
theorem SpecLaw.opSum {T₁ : OpTraits ⟨O₁, T⟩} {T₂ : OpTraits ⟨O₂, T⟩}
    [DialectDenoteM (⟨O₁, T⟩ : Dialect) Option] [DialectDenoteM (⟨O₂, T⟩ : Dialect) Option]
    (h₁ : SpecLaw T₁) (h₂ : SpecLaw T₂) : SpecLaw (T₁.opSum T₂)
  | .inl o, h, args => h₁ o h args
  | .inr o, h, args => h₂ o h args

/-- The purity laws of two dialects give the purity law of their operation sum. -/
theorem PureLaw.opSum {T₁ : OpTraits ⟨O₁, T⟩} {T₂ : OpTraits ⟨O₂, T⟩}
    {M : Type → Type} [Monad M]
    [DialectDenote (⟨O₁, T⟩ : Dialect)] [DialectDenote (⟨O₂, T⟩ : Dialect)]
    [DialectDenoteM (⟨O₁, T⟩ : Dialect) M] [DialectDenoteM (⟨O₂, T⟩ : Dialect) M]
    (h₁ : PureLaw T₁ M) (h₂ : PureLaw T₂ M) : PureLaw (T₁.opSum T₂) M
  | .inl o, h, args => h₁ o h args
  | .inr o, h, args => h₂ o h args

end SumLaws

/-- The constant law carries over to the re-typed dialect. -/
theorem ConstLaw.retype {d : Dialect.{0, 0}} [DialectSignature d] {T : OpTraits d}
    {τ : Type} (m : d.Ty → τ) (h : ConstLaw T) :
    letI := DialectOpSum.retypeSignature (d := d) m
    ConstLaw (T.retype τ) :=
  fun op hc => by
    show (DialectSignature.sig (d := d) op).map m = []
    rw [h op hc]
    rfl

/-! ## 5. Leakage along the inclusion of a re-typed dialect -/

namespace DialectOpSum

open ComParametricityTransport

variable {T : Type} [TyDenote T] {d : Dialect.{0, 0}} {O₂ : Type} [TyDenote d.Ty]
  [DialectSignature d] [DialectSignature (⟨O₂, T⟩ : Dialect)]

/-- The readings of transported argument values are the readings of the source
    argument values, when the reading of the target commutes with the embedding. -/
theorem valsNat_mapArgsVia (E : TyEmbedding d.Ty T) (L : LeakModel d)
    {Γ : Ctxt d} :
    letI := retypeSignature (d := d) E.map
    ∀ (L' : LeakModel (Dialect.opSum (d.retype T) ⟨O₂, T⟩)),
    (∀ (t : d.Ty) (x : ⟦t⟧), L'.valNat (E.map t) (E.trans x) = L.valNat t x) →
    ∀ {ts : List d.Ty} (args : HVector (fun t => Var Γ t) ts) (V : Valuation Γ),
      valsNat L' (Expr.lookupArgs (d := ⟨d.Op ⊕ O₂, T⟩) (mapArgsVia E.map args)
        (mapValVia E V)) = valsNat L (Expr.lookupArgs args V)
  | _, _, [], .nil, _ => rfl
  | L', hv, _ :: _, .cons a as, V => by
      let := retypeSignature (d := d) E.map
      show L'.valNat _ ((mapVarVia E.map a).lookup (mapValVia E V)) :: _ =
        L.valNat _ (a.lookup V) :: _
      rw [lookup_mapVarVia E a V, hv, valsNat_mapArgsVia E L L' hv as V]

/-- **Leakage along `inlVia`.** If a leakage model of the operation sum gives each
    left operation the kind it has in `d`, and reads a transported value as `d`
    reads the source value, then the events of the included program from the
    transported valuation are the events of the source program. -/
theorem ctLeak_inlVia (E : TyEmbedding d.Ty T) [DialectDenote d]
    [DialectDenote (⟨O₂, T⟩ : Dialect)] (L : LeakModel d) :
    letI := retypeSignature (d := d) E.map
    letI := retypeDenote (d := d) E
    ∀ (L' : LeakModel (Dialect.opSum (d.retype T) ⟨O₂, T⟩)),
      (∀ op : d.Op, L'.kind (.inl op) = L.kind op) →
      (∀ (t : d.Ty) (x : ⟦t⟧), L'.valNat (E.map t) (E.trans x) = L.valNat t x) →
      ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (V : Valuation Γ),
        ComLevelCheck.Com.ctLeak L' ((inlVia (O₂ := O₂) E).lowerCom c) (mapValVia E V)
          = ComLevelCheck.Com.ctLeak L c V := by
  let := retypeSignature (d := d) E.map
  let := retypeDenote (d := d) E
  intro L' hk hv Γ t c
  induction c with
  | ret v => intro V; rfl
  | var e body ih =>
      intro V
      obtain ⟨op, hop, args⟩ := e
      subst hop
      show ComLevelCheck.Expr.ctLeak L' _ (mapValVia E V) ++
          ComLevelCheck.Com.ctLeak L' _ _ =
        ComLevelCheck.Expr.ctLeak L ⟨op, rfl, args⟩ V ++ ComLevelCheck.Com.ctLeak L body _
      congr 1
      · show opLeak L' (.inl op) (Expr.lookupArgs (d := ⟨d.Op ⊕ O₂, T⟩)
            (mapArgsVia E.map args) (mapValVia E V)) = opLeak L op (Expr.lookupArgs args V)
        unfold opLeak
        rw [hk, valsNat_mapArgsVia E L L' hv args V]
      · rw [← ih]
        congr 1
        show HVector.cons _ _ = HVector.cons _ _
        congr 1
        show E.trans (DialectDenote.denote (d := d) op (unmapArgs E (Expr.lookupArgs
          (d := ⟨d.Op ⊕ O₂, T⟩) (mapArgsVia E.map args) (mapValVia E V)))) = _
        rw [lookupArgs_mapArgsVia E args V]
        rfl

end DialectOpSum

end CatCrypt.Crypto.SecureCompilation.VIR
