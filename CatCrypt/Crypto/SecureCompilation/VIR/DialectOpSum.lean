/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# Operation sum of VIR dialects over a shared type alphabet

`Com` is indexed by a single dialect (`VIR/Core.lean`). The operation sum
`Dialect.opSum d e` of two dialects with the same type alphabet `T` has
`Op := d.Op ⊕ e.Op` and `Ty := T`, so one program interleaves operations of both
summands and a value produced by an operation of one summand is an operand of an
operation of the other. Its signature and denotation are case splits delegating
to the summand, and each summand includes into it by a structural lowering
(`ComParametricityTransport.LoweringData`) that preserves denotation.

Two dialects whose type alphabets differ but embed into a common alphabet `T` are
first re-typed into `T` along a `TyEmbedding` (`Dialect.retype`,
`retypeSignature`, `retypeDenote`); the operation sum of the re-typed dialects is
again a `Dialect.opSum`, and the inclusions `inlVia` / `inrVia` go from the
original dialects into it with the embedding as their type map.

`Dialect.sum` (`VIR/DialectCoproduct.lean`) is the coproduct with disjoint type
alphabets, in which no value crosses between the summands.

## Main definitions

* `Dialect.opSum`: the operation sum of two dialects.
* `DialectOpSum.instDialectSignatureOpSum`, `DialectOpSum.instDialectDenoteOpSum`:
  its signature and denotation, each a case split over the tag.
* `DialectOpSum.inl` / `DialectOpSum.inr`: the two inclusions as `LoweringData`.
* `TyEmbedding`, `Dialect.retype`, `DialectOpSum.retypeSignature`,
  `DialectOpSum.retypeDenote`: a dialect carried into a larger type alphabet.
* `DialectOpSum.inlVia` / `DialectOpSum.inrVia`: the inclusions of the original
  dialects into the operation sum of their re-typed copies.

## Main results

* `DialectOpSum.inl_fundamental` / `DialectOpSum.inr_fundamental`: whole-program
  denotation preservation of the two inclusions, from
  `ComParametricityTransport.fundamental`.
* `DialectOpSum.inlVia_fundamental` / `DialectOpSum.inrVia_fundamental`: the same
  for the inclusions along a type embedding.
* `DialectOpSum.Witness.mixedProg_denote`: the denotation of a program mixing a
  `catCryptDialect` operation with the two operations of a test dialect over
  `CryptoTy`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

universe u v

open Ctxt (Var Valuation)

/-! ## 1. The operation sum and the re-typed dialect -/

/-- The operation sum of two dialects: the operations are the tagged sum of the two
    operation alphabets, the type alphabet is that of `d`. Its instances apply when
    `e` has the same type alphabet. -/
@[reducible] def Dialect.opSum (d e : Dialect.{u, v}) : Dialect.{u, v} where
  Op := d.Op ⊕ e.Op
  Ty := d.Ty

/-- The dialect `d` with its operations kept and its type alphabet replaced by
    `T`. Its signature and denotation are given along a type embedding
    (`DialectOpSum.retypeSignature`, `DialectOpSum.retypeDenote`). -/
@[reducible] def Dialect.retype (d : Dialect.{u, v}) (T : Type v) : Dialect.{u, v} where
  Op := d.Op
  Ty := T

/-- An embedding of a type alphabet `σ` into a type alphabet `τ`: a map on types
    with value transports in both directions, the backward one a left inverse of
    the forward one. -/
structure TyEmbedding (σ τ : Type) [TyDenote σ] [TyDenote τ] where
  /-- The map on types. -/
  map : σ → τ
  /-- The forward value transport. -/
  trans : ∀ {t : σ}, ⟦t⟧ → ⟦map t⟧
  /-- The backward value transport. -/
  untrans : ∀ {t : σ}, ⟦map t⟧ → ⟦t⟧
  /-- The backward transport is a left inverse of the forward one. -/
  untrans_trans : ∀ {t : σ} (x : ⟦t⟧), untrans (trans x) = x

namespace DialectOpSum

open ComParametricityTransport

/-! ## 2. Signature and denotation of the operation sum -/

section Instances

variable {O₁ O₂ : Type} {T : Type}

/-- Signatures in the operation sum: the summand's argument list and return type,
    unchanged, since both summands have the type alphabet `T`. -/
@[reducible] instance instDialectSignatureOpSum
    [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectSignature (⟨O₂, T⟩ : Dialect)] :
    DialectSignature (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) where
  sig op := match op with
    | .inl o => DialectSignature.sig (d := ⟨O₁, T⟩) o
    | .inr o => DialectSignature.sig (d := ⟨O₂, T⟩) o
  ret op := match op with
    | .inl o => DialectSignature.ret (d := ⟨O₁, T⟩) o
    | .inr o => DialectSignature.ret (d := ⟨O₂, T⟩) o

/-- Operation denotation in the operation sum: the summand's denotation. -/
instance instDialectDenoteOpSum [TyDenote T]
    [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectDenote (⟨O₁, T⟩ : Dialect)]
    [DialectSignature (⟨O₂, T⟩ : Dialect)] [DialectDenote (⟨O₂, T⟩ : Dialect)] :
    DialectDenote (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) where
  denote op := match op with
    | .inl o => fun args => DialectDenote.denote (d := ⟨O₁, T⟩) o args
    | .inr o => fun args => DialectDenote.denote (d := ⟨O₂, T⟩) o args

end Instances

/-! ## 3. The inclusions over the shared alphabet -/

section Shared

variable {O O' O₁ O₂ : Type} {T : Type}

/-- A variable of a dialect over `T`, read as a variable of another dialect over
    `T` in the same context. -/
def castVar : {Γ : List T} → {t : T} →
    Var (d := ⟨O, T⟩) Γ t → Var (d := ⟨O', T⟩) Γ t
  | _, _, .here => .here
  | _, _, .there v => .there (castVar v)

/-- An argument vector of variables, read in another dialect over `T`. -/
def castArgs {Γ : List T} : {ts : List T} →
    HVector (fun t => Var (d := ⟨O, T⟩) Γ t) ts →
    HVector (fun t => Var (d := ⟨O', T⟩) Γ t) ts
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (castVar v) (castArgs vs)

/-- Looking up a cast variable gives the lookup of the original variable. -/
theorem lookup_castVar [TyDenote T] :
    ∀ {Γ : List T} {t : T} (v : Var (d := ⟨O, T⟩) Γ t) (V : Valuation (d := ⟨O, T⟩) Γ),
      (castVar (O' := O') v).lookup (d := ⟨O', T⟩) V = v.lookup V
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ xs => lookup_castVar v xs

/-- Resolving cast arguments gives the resolution of the original arguments. -/
theorem lookupArgs_castArgs [TyDenote T] {Γ : List T} :
    ∀ {ts : List T} (args : HVector (fun t => Var (d := ⟨O, T⟩) Γ t) ts)
      (V : Valuation (d := ⟨O, T⟩) Γ),
      Expr.lookupArgs (d := ⟨O', T⟩) (castArgs args) V = Expr.lookupArgs args V
  | [], .nil, _ => rfl
  | _ :: _, .cons v vs, V => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookup_castVar v V, lookupArgs_castArgs vs V]

variable [DialectSignature (⟨O₁, T⟩ : Dialect)] [DialectSignature (⟨O₂, T⟩ : Dialect)]

/-- The inclusion of the left summand into the operation sum as a structural
    lowering: types and contexts are unchanged, each operation is tagged `.inl`. -/
def inl : LoweringData ⟨O₁, T⟩ (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) where
  mapTy := fun t => t
  mapCtx := fun Γ => Γ
  mapCtx_cons := fun _ _ => rfl
  mapVar := castVar
  lowerExpr := fun ex =>
    { op := .inl ex.op
      retTy_eq := ex.retTy_eq
      args := castArgs ex.args }

/-- The inclusion of the right summand into the operation sum as a structural
    lowering: types and contexts are unchanged, each operation is tagged `.inr`. -/
def inr : LoweringData ⟨O₂, T⟩ (Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) where
  mapTy := fun t => t
  mapCtx := fun Γ => Γ
  mapCtx_cons := fun _ _ => rfl
  mapVar := castVar
  lowerExpr := fun ex =>
    { op := .inr ex.op
      retTy_eq := ex.retTy_eq
      args := castArgs ex.args }

variable [TyDenote T] [DialectDenote (⟨O₁, T⟩ : Dialect)]
  [DialectDenote (⟨O₂, T⟩ : Dialect)]

/-- The value transport of the left inclusion: the identity. -/
def inlTransTy : TransTy (inl (O₁ := O₁) (O₂ := O₂) (T := T)) := fun x => x

/-- The valuation transport of the left inclusion: the identity. -/
def inlMapVal : MapVal (inl (O₁ := O₁) (O₂ := O₂) (T := T)) := fun V => V

/-- The value transport of the right inclusion: the identity. -/
def inrTransTy : TransTy (inr (O₁ := O₁) (O₂ := O₂) (T := T)) := fun x => x

/-- The valuation transport of the right inclusion: the identity. -/
def inrMapVal : MapVal (inr (O₁ := O₁) (O₂ := O₂) (T := T)) := fun V => V

/-- Whole-program denotation preservation for the left inclusion: a program over
    the left summand, included into the operation sum, denotes under the same
    valuation to the same value. -/
theorem inl_fundamental {Γ : List T} {t : T} (c : Com ⟨O₁, T⟩ Γ t) :
    ComLowerTransports (inl (O₂ := O₂)) inlTransTy inlMapVal c :=
  fundamental _ _ _ (fun v V => lookup_castVar v V)
    (by
      intro Γ t ex V
      obtain ⟨op, rfl, args⟩ := ex
      show DialectDenote.denote (d := ⟨O₁, T⟩) op
          (Expr.lookupArgs (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (castArgs args) V) = _
      rw [lookupArgs_castArgs args V]
      rfl)
    (fun _ _ => rfl) c

/-- Whole-program denotation preservation for the right inclusion. -/
theorem inr_fundamental {Γ : List T} {t : T} (c : Com ⟨O₂, T⟩ Γ t) :
    ComLowerTransports (inr (O₁ := O₁)) inrTransTy inrMapVal c :=
  fundamental _ _ _ (fun v V => lookup_castVar v V)
    (by
      intro Γ t ex V
      obtain ⟨op, rfl, args⟩ := ex
      show DialectDenote.denote (d := ⟨O₂, T⟩) op
          (Expr.lookupArgs (d := Dialect.opSum ⟨O₁, T⟩ ⟨O₂, T⟩) (castArgs args) V) = _
      rw [lookupArgs_castArgs args V]
      rfl)
    (fun _ _ => rfl) c

end Shared

/-! ## 4. Re-typing a dialect along a type embedding -/

section Retype

variable {d : Dialect.{0, 0}} {T : Type}

/-- Signatures of the re-typed dialect: the argument list and return type carried
    along the type map. -/
@[reducible] def retypeSignature [DialectSignature d] (m : d.Ty → T) :
    DialectSignature (d.retype T) where
  sig o := (DialectSignature.sig (d := d) o).map m
  ret o := m (DialectSignature.ret (d := d) o)

variable [TyDenote d.Ty] [TyDenote T]

/-- Re-index an argument vector out of the larger alphabet by the backward value
    transport. -/
def unmapArgs (E : TyEmbedding d.Ty T) :
    {ts : List d.Ty} → HVector (fun t => ⟦t⟧) (ts.map E.map) → HVector (fun t => ⟦t⟧) ts
  | [], _ => .nil
  | t :: _, .cons x xs => .cons (E.untrans (t := t) x) (unmapArgs E xs)

/-- Operation denotation of the re-typed dialect: re-index the arguments into the
    original alphabet, apply the original denotation, and transport the result. -/
@[reducible] def retypeDenote [DialectSignature d] [DialectDenote d]
    (E : TyEmbedding d.Ty T) :
    letI := retypeSignature (d := d) E.map
    DialectDenote (d.retype T) :=
  letI := retypeSignature (d := d) E.map
  { denote := fun o args => E.trans (DialectDenote.denote (d := d) o (unmapArgs E args)) }

/-- Transport a variable into the context carried along the type map, in any
    dialect over `T`. -/
def mapVarVia {O : Type} (m : d.Ty → T) : {Γ : Ctxt d} → {t : d.Ty} →
    Var Γ t → Var (d := ⟨O, T⟩) (Γ.map m) (m t)
  | _, _, .here => .here
  | _, _, .there v => .there (mapVarVia m v)

/-- Transport an argument vector of variables into the context carried along the
    type map. -/
def mapArgsVia {O : Type} (m : d.Ty → T) {Γ : Ctxt d} : {ts : List d.Ty} →
    HVector (fun t => Var Γ t) ts →
    HVector (fun t => Var (d := ⟨O, T⟩) (Γ.map m) t) (ts.map m)
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (mapVarVia m v) (mapArgsVia m vs)

/-- Transport a valuation into the context carried along the embedding. -/
def mapValVia {O : Type} (E : TyEmbedding d.Ty T) : {Γ : Ctxt d} →
    Valuation Γ → Valuation (d := ⟨O, T⟩) (Γ.map E.map)
  | [], _ => .nil
  | _ :: _, .cons x xs => .cons (E.trans x) (mapValVia E xs)

/-- Looking up a transported variable in a transported valuation gives the
    transport of the source lookup. -/
theorem lookup_mapVarVia {O : Type} (E : TyEmbedding d.Ty T) :
    ∀ {Γ : Ctxt d} {t : d.Ty} (v : Var Γ t) (V : Valuation Γ),
      (mapVarVia (O := O) E.map v).lookup (mapValVia E V) = E.trans (v.lookup V)
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ xs => lookup_mapVarVia E v xs

/-- Resolving transported arguments against a transported valuation and
    re-indexing gives the source argument values. -/
theorem lookupArgs_mapArgsVia {O : Type} (E : TyEmbedding d.Ty T) {Γ : Ctxt d} :
    ∀ {ts : List d.Ty} (args : HVector (fun t => Var Γ t) ts) (V : Valuation Γ),
      unmapArgs E (Expr.lookupArgs (d := ⟨O, T⟩) (mapArgsVia E.map args) (mapValVia E V))
        = Expr.lookupArgs args V
  | [], .nil, _ => rfl
  | _ :: _, .cons v vs, V => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookup_mapVarVia E v V, E.untrans_trans, lookupArgs_mapArgsVia E vs V]

end Retype

/-! ## 5. The inclusions along a type embedding -/

section Via

variable {T : Type} [TyDenote T]

section Left

variable {d : Dialect.{0, 0}} {O₂ : Type} [TyDenote d.Ty] [DialectSignature d]
  [DialectSignature (⟨O₂, T⟩ : Dialect)]

/-- The inclusion of `d` into the operation sum of its re-typed copy with a
    dialect over `T`: types and contexts are carried along the embedding, each
    operation is tagged `.inl`. -/
def inlVia (E : TyEmbedding d.Ty T) :
    letI := retypeSignature (d := d) E.map
    LoweringData d (Dialect.opSum (d.retype T) ⟨O₂, T⟩) :=
  letI := retypeSignature (d := d) E.map
  { mapTy := E.map
    mapCtx := List.map E.map
    mapCtx_cons := fun _ _ => rfl
    mapVar := mapVarVia E.map
    lowerExpr := fun ex =>
      { op := .inl ex.op
        retTy_eq := congrArg E.map ex.retTy_eq
        args := mapArgsVia E.map ex.args } }

variable [DialectDenote d] [DialectDenote (⟨O₂, T⟩ : Dialect)]

/-- The value transport of `inlVia E`: the forward value transport of `E`. -/
def inlViaTransTy (E : TyEmbedding d.Ty T) :
    letI := retypeSignature (d := d) E.map
    letI := retypeDenote (d := d) E
    TransTy (inlVia (O₂ := O₂) E) :=
  fun x => E.trans x

/-- The valuation transport of `inlVia E`. -/
def inlViaMapVal (E : TyEmbedding d.Ty T) :
    letI := retypeSignature (d := d) E.map
    letI := retypeDenote (d := d) E
    MapVal (inlVia (O₂ := O₂) E) :=
  fun V => mapValVia E V

/-- Whole-program denotation preservation for `inlVia E`. -/
theorem inlVia_fundamental (E : TyEmbedding d.Ty T) {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) :
    letI := retypeSignature (d := d) E.map
    letI := retypeDenote (d := d) E
    ComLowerTransports (inlVia E) (inlViaTransTy E) (inlViaMapVal (O₂ := O₂) E) c :=
  letI := retypeSignature (d := d) E.map
  letI := retypeDenote (d := d) E
  fundamental _ _ _ (fun v V => lookup_mapVarVia E v V)
    (by
      intro Γ t ex V
      obtain ⟨op, rfl, args⟩ := ex
      show E.trans (DialectDenote.denote (d := d) op
          (unmapArgs E (Expr.lookupArgs (d := ⟨d.Op ⊕ O₂, T⟩) (mapArgsVia E.map args)
            (mapValVia E V)))) = _
      rw [lookupArgs_mapArgsVia E args V]
      rfl)
    (fun _ _ => rfl) c

end Left

section Right

variable {e : Dialect.{0, 0}} {O₁ : Type} [TyDenote e.Ty] [DialectSignature e]
  [DialectSignature (⟨O₁, T⟩ : Dialect)]

/-- The inclusion of `e` into the operation sum of a dialect over `T` with the
    re-typed copy of `e`: types and contexts are carried along the embedding, each
    operation is tagged `.inr`. -/
def inrVia (E : TyEmbedding e.Ty T) :
    letI := retypeSignature (d := e) E.map
    LoweringData e (Dialect.opSum ⟨O₁, T⟩ (e.retype T)) :=
  letI := retypeSignature (d := e) E.map
  { mapTy := E.map
    mapCtx := List.map E.map
    mapCtx_cons := fun _ _ => rfl
    mapVar := mapVarVia E.map
    lowerExpr := fun ex =>
      { op := .inr ex.op
        retTy_eq := congrArg E.map ex.retTy_eq
        args := mapArgsVia E.map ex.args } }

variable [DialectDenote e] [DialectDenote (⟨O₁, T⟩ : Dialect)]

/-- The value transport of `inrVia E`: the forward value transport of `E`. -/
def inrViaTransTy (E : TyEmbedding e.Ty T) :
    letI := retypeSignature (d := e) E.map
    letI := retypeDenote (d := e) E
    TransTy (inrVia (O₁ := O₁) E) :=
  fun x => E.trans x

/-- The valuation transport of `inrVia E`. -/
def inrViaMapVal (E : TyEmbedding e.Ty T) :
    letI := retypeSignature (d := e) E.map
    letI := retypeDenote (d := e) E
    MapVal (inrVia (O₁ := O₁) E) :=
  fun V => mapValVia E V

/-- Whole-program denotation preservation for `inrVia E`. -/
theorem inrVia_fundamental (E : TyEmbedding e.Ty T) {Γ : Ctxt e} {t : e.Ty}
    (c : Com e Γ t) :
    letI := retypeSignature (d := e) E.map
    letI := retypeDenote (d := e) E
    ComLowerTransports (inrVia E) (inrViaTransTy E) (inrViaMapVal (O₁ := O₁) E) c :=
  letI := retypeSignature (d := e) E.map
  letI := retypeDenote (d := e) E
  fundamental _ _ _ (fun v V => lookup_mapVarVia E v V)
    (by
      intro Γ t ex V
      obtain ⟨op, rfl, args⟩ := ex
      show E.trans (DialectDenote.denote (d := e) op
          (unmapArgs E (Expr.lookupArgs (d := ⟨O₁ ⊕ e.Op, T⟩) (mapArgsVia E.map args)
            (mapValVia E V)))) = _
      rw [lookupArgs_mapArgsVia E args V]
      rfl)
    (fun _ _ => rfl) c

end Right

end Via

/-! ## 6. A program mixing `catCryptDialect` with a test dialect

A two-operation dialect over `CryptoTy`, summed with `catCryptDialect`. In the
program below a `catCryptDialect` addition consumes a test-dialect result and a
test-dialect zero test consumes the addition's result. -/

namespace Witness

open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (catCryptDialect)

/-- The operations of the test dialect. -/
inductive TestOp where
  /-- Doubling of a `w`-bit word. -/
  | dbl (w : Nat)
  /-- The zero test of a `w`-bit word. -/
  | isZero (w : Nat)

/-- The test dialect: `Op` is `TestOp`, `Ty` is `CryptoTy`. -/
@[reducible] def testDialect : Dialect := { Op := TestOp, Ty := CryptoTy }

instance : DialectSignature testDialect where
  sig
    | .dbl w => [.sword w]
    | .isZero w => [.sword w]
  ret
    | .dbl w => .sword w
    | .isZero _ => .bit

instance : DialectDenote testDialect where
  denote
    | .dbl w => fun args =>
        let a : BitVec w := args.head
        a + a
    | .isZero w => fun args =>
        let a : BitVec w := args.head
        decide (a = 0)

/-- The operation sum of `catCryptDialect` and the test dialect. -/
@[reducible] def mixedDialect : Dialect := Dialect.opSum catCryptDialect testDialect

/-- A three-binding program over the operation sum, with one `sword 8` input `x`:

    ```
    let b : sword 8 = inr (dbl 8) x
    let c : sword 8 = inl (bvAdd 8) b x
    let z : bit     = inr (isZero 8) c
    ret z
    ``` -/
def mixedProg : Com mixedDialect [CryptoTy.sword 8] CryptoTy.bit :=
  .var (t := CryptoTy.sword 8) ⟨.inr (.dbl 8), rfl, .cons .here .nil⟩
    (.var (t := CryptoTy.sword 8)
        ⟨.inl (.bvAdd 8), rfl, .cons .here (.cons (.there .here) .nil)⟩
      (.var (t := CryptoTy.bit) ⟨.inr (.isZero 8), rfl, .cons .here .nil⟩
        (.ret .here)))

/-- `mixedProg` denotes to the zero test of `x + x + x`. -/
theorem mixedProg_denote (x : BitVec 8) :
    mixedProg.denote (.cons x .nil) = decide (x + x + x = 0) := rfl

end Witness

end DialectOpSum

end CatCrypt.Crypto.SecureCompilation.VIR
