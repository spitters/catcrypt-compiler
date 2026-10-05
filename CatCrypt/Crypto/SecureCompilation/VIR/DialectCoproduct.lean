/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport

/-!
# Coproduct of VIR dialects

`Com` is indexed by a single dialect (`VIR/Core.lean`), so one program draws its
operations from one `Op` alphabet and its types from one `Ty` alphabet. The
coproduct dialect `d ⊕ e` has `Op := d.Op ⊕ e.Op` and `Ty := d.Ty ⊕ e.Ty`, so a
single `Com` over it interleaves operations of both summands, and each summand
includes into it by a structural lowering
(`ComParametricityTransport.LoweringData`) that preserves denotation.

The two type alphabets remain disjoint: a value produced by a `d` operation has
a type in the `.inl` half and is consumed only by another `d` operation. Two
dialects whose operations exchange values need a common type alphabet; that
case is the operation sum `Dialect.opSum` (`VIR/DialectOpSum.lean`), which tags
`Op` alone and leaves `Ty` untouched, with instances `VIR/MlirArithScfSum.lean`
and `VIR/FieldCmpSum.lean`. The construction here covers the case where the two
`Ty` alphabets stay disjoint.

`Dialect.sum` has one consumer: the field front translates hax normal form into
`nfFieldDialect = Dialect.sum nfDialect fieldDialect` (`Hax/NFFieldSum.lean`). `VIR/DialectCategory.lean` describes its place among
the constructions on dialects.

`LoweringData` composes (`VIR/LoweringDataComp.lean`: `L1.comp L2`,
`comp_fundamental`), so an inclusion followed by a lowering out of the coproduct
is a single `LoweringData` whose whole-program transport square is
`comp_fundamental`.

## Main definitions

* `Dialect.sum`, with notation `d ⊕ e`: the coproduct dialect.
* `instTyDenoteSum`, `instDialectSignatureSum`, `instDialectDenoteSum`: the type
  denotation, operation signature and operation denotation of the coproduct,
  each a case-split delegating to the summand.
* `unmapInl` / `unmapInr`: re-index an `HVector` along `List.map Sum.inl` /
  `List.map Sum.inr`, which is how the coproduct's `DialectDenote` feeds a
  summand's `denote`.
* `mapVarInl` / `mapArgsInl` / `mapValInl` and their `inr` twins: the variable,
  argument-vector and valuation transports along an injection.
* `inlLowering` / `inrLowering`: the two inclusions as `LoweringData`.
* `inlTransTy` / `inlMapVal` and their `inr` twins: the value and valuation
  transports carried by the inclusions.

## Main results

* `inl_denote` / `inr_denote`: whole-program denotation preservation for the two
  inclusions, from `ComParametricityTransport.fundamental` applied to the three
  leaf coherences (`inl_varTransports`, `inl_opTransports`,
  `inl_mapValExtends`).
* `Witness.mixedProg_denote`: a three-binding program over a concrete coproduct
  of a `Nat`-valued and a `Bool`-valued dialect, using an operation of each
  summand, with a left-summand variable read across an intervening
  right-summand binding.
* `Witness.inl_numProg_denote`: the left inclusion's transport square
  instantiated at a concrete two-binding source program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

universe u v

open Ctxt (Var Valuation)

/-! ## 1. The coproduct dialect -/

/-- The coproduct of two dialects: the operations are the tagged sum of the two
    operation alphabets, the types the tagged sum of the two type alphabets. It is a
    presentation with no consumer in the compilation pipeline. -/
@[reducible] def Dialect.sum (d e : Dialect.{u, v}) : Dialect.{u, v} where
  Op := d.Op ⊕ e.Op
  Ty := d.Ty ⊕ e.Ty

@[inherit_doc] scoped infixr:30 " ⊕ " => Dialect.sum

namespace DialectCoproduct

open ComParametricityTransport

variable {d e : Dialect}

/-! ## 2. Instances

Each instance is a case-split delegating to the summand. `Dialect.sum` is
`@[reducible]` so that instance search reduces `(d ⊕ e).Ty` to `d.Ty ⊕ e.Ty`. -/

/-- Denotation of a sum type alphabet: each tag denotes as it does in its
    summand. -/
instance instTyDenoteSum {σ τ : Type v} [TyDenote σ] [TyDenote τ] :
    TyDenote (σ ⊕ τ) where
  denote
    | .inl t => ⟦t⟧
    | .inr t => ⟦t⟧

/-- Signatures in the coproduct: a summand's argument list and return type,
    re-tagged by the corresponding injection. -/
instance instDialectSignatureSum [DialectSignature d] [DialectSignature e] :
    DialectSignature (d ⊕ e) where
  sig
    | .inl o => (DialectSignature.sig o).map .inl
    | .inr o => (DialectSignature.sig o).map .inr
  ret
    | .inl o => .inl (DialectSignature.ret o)
    | .inr o => .inr (DialectSignature.ret o)

/-- Re-index an argument vector along `Sum.inl`: an `HVector` over
    `ts.map Sum.inl` is an `HVector` over `ts`, entrywise, because `⟦.inl t⟧`
    and `⟦t⟧` are the same type. -/
def unmapInl [TyDenote d.Ty] [TyDenote e.Ty] :
    {ts : List d.Ty} →
      HVector (fun t => ⟦t⟧) (ts.map (Sum.inl (β := e.Ty))) →
      HVector (fun t => ⟦t⟧) ts
  | [], _ => .nil
  | _ :: _, .cons x xs => .cons x (unmapInl xs)

/-- Re-index an argument vector along `Sum.inr`. -/
def unmapInr [TyDenote d.Ty] [TyDenote e.Ty] :
    {ts : List e.Ty} →
      HVector (fun t => ⟦t⟧) (ts.map (Sum.inr (α := d.Ty))) →
      HVector (fun t => ⟦t⟧) ts
  | [], _ => .nil
  | _ :: _, .cons x xs => .cons x (unmapInr xs)

/-- Operation denotation in the coproduct: strip the tag from the arguments and
    apply the summand's denotation. -/
instance instDialectDenoteSum
    [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
    [TyDenote e.Ty] [DialectSignature e] [DialectDenote e] :
    DialectDenote (d ⊕ e) where
  denote
    | .inl o => fun args => DialectDenote.denote o (unmapInl args)
    | .inr o => fun args => DialectDenote.denote o (unmapInr args)

/-! ## 3. Syntactic transport along an injection -/

/-- Transport a variable into the left-injected context. -/
def mapVarInl : {Γ : Ctxt d} → {t : d.Ty} →
    Var Γ t → Var (d := d ⊕ e) (Γ.map Sum.inl) (Sum.inl t)
  | _, _, .here => .here
  | _, _, .there v => .there (mapVarInl v)

/-- Transport an argument vector of variables into the left-injected
    context. -/
def mapArgsInl {Γ : Ctxt d} : {ts : List d.Ty} →
    HVector (fun t => Var Γ t) ts →
    HVector (fun t => Var (d := d ⊕ e) (Γ.map Sum.inl) t) (ts.map Sum.inl)
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (mapVarInl v) (mapArgsInl vs)

/-- Transport a variable into the right-injected context. -/
def mapVarInr : {Γ : Ctxt e} → {t : e.Ty} →
    Var Γ t → Var (d := d ⊕ e) (Γ.map Sum.inr) (Sum.inr t)
  | _, _, .here => .here
  | _, _, .there v => .there (mapVarInr v)

/-- Transport an argument vector of variables into the right-injected
    context. -/
def mapArgsInr {Γ : Ctxt e} : {ts : List e.Ty} →
    HVector (fun t => Var Γ t) ts →
    HVector (fun t => Var (d := d ⊕ e) (Γ.map Sum.inr) t) (ts.map Sum.inr)
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (mapVarInr v) (mapArgsInr vs)

/-! ## 4. The two inclusions as structural lowerings -/

section Lowering

variable [DialectSignature d] [DialectSignature e]

/-- The inclusion of the left summand into the coproduct as a structural
    lowering: types and contexts are injected by `Sum.inl`, each operation is
    re-tagged. -/
def inlLowering (d e : Dialect) [DialectSignature d] [DialectSignature e] :
    LoweringData d (d ⊕ e) where
  mapTy := Sum.inl
  mapCtx := List.map Sum.inl
  mapCtx_cons := fun _ _ => rfl
  mapVar := mapVarInl
  lowerExpr := fun ex =>
    { op := .inl ex.op
      retTy_eq := congrArg Sum.inl ex.retTy_eq
      args := mapArgsInl ex.args }

/-- The inclusion of the right summand into the coproduct as a structural
    lowering. -/
def inrLowering (d e : Dialect) [DialectSignature d] [DialectSignature e] :
    LoweringData e (d ⊕ e) where
  mapTy := Sum.inr
  mapCtx := List.map Sum.inr
  mapCtx_cons := fun _ _ => rfl
  mapVar := mapVarInr
  lowerExpr := fun ex =>
    { op := .inr ex.op
      retTy_eq := congrArg Sum.inr ex.retTy_eq
      args := mapArgsInr ex.args }

end Lowering

/-! ## 5. The leaf coherences

Both value transports are the identity: `⟦.inl t⟧` is `⟦t⟧` by the case-split in
`instTyDenoteSum`. The valuation transport re-indexes along `List.map`, the
inverse of `unmapInl`. -/

section Transport

variable [TyDenote d.Ty] [TyDenote e.Ty]

/-- Re-index a valuation along `Sum.inl`, the inverse of `unmapInl`. -/
def mapValInl : {Γ : Ctxt d} →
    Valuation Γ → Valuation (d := d ⊕ e) (Γ.map Sum.inl)
  | [], _ => .nil
  | _ :: _, .cons x xs => .cons x (mapValInl xs)

/-- Re-index a valuation along `Sum.inr`, the inverse of `unmapInr`. -/
def mapValInr : {Γ : Ctxt e} →
    Valuation Γ → Valuation (d := d ⊕ e) (Γ.map Sum.inr)
  | [], _ => .nil
  | _ :: _, .cons x xs => .cons x (mapValInr xs)

/-- Looking up a left-injected variable in a left-injected valuation gives the
    source lookup. -/
theorem lookup_mapVarInl :
    ∀ {Γ : Ctxt d} {t : d.Ty} (v : Var Γ t) (V : Valuation Γ),
      (mapVarInl (e := e) v).lookup (mapValInl V) = v.lookup V
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ xs => lookup_mapVarInl v xs

/-- Looking up a right-injected variable in a right-injected valuation gives the
    source lookup. -/
theorem lookup_mapVarInr :
    ∀ {Γ : Ctxt e} {t : e.Ty} (v : Var Γ t) (V : Valuation Γ),
      (mapVarInr (d := d) v).lookup (mapValInr V) = v.lookup V
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ xs => lookup_mapVarInr v xs

/-- Resolving left-injected arguments against a left-injected valuation and
    stripping the tags gives the source argument values. -/
theorem lookupArgs_mapArgsInl {Γ : Ctxt d} :
    ∀ {ts : List d.Ty} (args : HVector (fun t => Var Γ t) ts) (V : Valuation Γ),
      unmapInl (e := e) (Expr.lookupArgs (mapArgsInl (e := e) args) (mapValInl V))
        = Expr.lookupArgs args V
  | [], .nil, _ => rfl
  | _ :: _, .cons v vs, V => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookup_mapVarInl v V, lookupArgs_mapArgsInl vs V]

/-- Resolving right-injected arguments against a right-injected valuation and
    stripping the tags gives the source argument values. -/
theorem lookupArgs_mapArgsInr {Γ : Ctxt e} :
    ∀ {ts : List e.Ty} (args : HVector (fun t => Var Γ t) ts) (V : Valuation Γ),
      unmapInr (d := d) (Expr.lookupArgs (mapArgsInr (d := d) args) (mapValInr V))
        = Expr.lookupArgs args V
  | [], .nil, _ => rfl
  | _ :: _, .cons v vs, V => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookup_mapVarInr v V, lookupArgs_mapArgsInr vs V]

variable [DialectSignature d] [DialectSignature e]

/-- The left inclusion's value transport: the identity. -/
def inlTransTy : TransTy (inlLowering d e) := fun x => x

/-- The left inclusion's valuation transport. -/
def inlMapVal : MapVal (inlLowering d e) := fun V => mapValInl V

/-- The right inclusion's value transport: the identity. -/
def inrTransTy : TransTy (inrLowering d e) := fun x => x

/-- The right inclusion's valuation transport. -/
def inrMapVal : MapVal (inrLowering d e) := fun V => mapValInr V

/-- Variable-transport coherence for the left inclusion. -/
theorem inl_varTransports :
    VarTransports (inlLowering d e) inlTransTy inlMapVal :=
  fun v V => lookup_mapVarInl v V

/-- Variable-transport coherence for the right inclusion. -/
theorem inr_varTransports :
    VarTransports (inrLowering d e) inrTransTy inrMapVal :=
  fun v V => lookup_mapVarInr v V

/-- Binding-threading coherence for the left inclusion. -/
theorem inl_mapValExtends :
    MapValExtends (inlLowering d e) inlTransTy inlMapVal := fun _ _ => rfl

/-- Binding-threading coherence for the right inclusion. -/
theorem inr_mapValExtends :
    MapValExtends (inrLowering d e) inrTransTy inrMapVal := fun _ _ => rfl

end Transport

/-! ## 6. Denotation preservation -/

section Denote

variable [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
variable [TyDenote e.Ty] [DialectSignature e] [DialectDenote e]

/-- Per-operation leaf transport for the left inclusion: a re-tagged operation
    denotes to the source operation's value. -/
theorem inl_opTransports :
    OpLowerTransports (inlLowering d e) inlTransTy inlMapVal := by
  intro Γ t ex V
  obtain ⟨op, rfl, args⟩ := ex
  show DialectDenote.denote op
      (unmapInl (Expr.lookupArgs (mapArgsInl args) (mapValInl V))) = _
  rw [lookupArgs_mapArgsInl args V]
  rfl

/-- Per-operation leaf transport for the right inclusion. -/
theorem inr_opTransports :
    OpLowerTransports (inrLowering d e) inrTransTy inrMapVal := by
  intro Γ t ex V
  obtain ⟨op, rfl, args⟩ := ex
  show DialectDenote.denote op
      (unmapInr (Expr.lookupArgs (mapArgsInr args) (mapValInr V))) = _
  rw [lookupArgs_mapArgsInr args V]
  rfl

/-- **Whole-program denotation preservation for the left inclusion.** Every
    `Com` over `d`, included into `d ⊕ e`, denotes under the injected valuation
    to the value it denotes over `d`. The three leaf coherences feed
    `ComParametricityTransport.fundamental`. -/
theorem inl_denote {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) :
    ComLowerTransports (inlLowering d e) inlTransTy inlMapVal c :=
  fundamental (inlLowering d e) inlTransTy inlMapVal
    inl_varTransports inl_opTransports inl_mapValExtends c

/-- **Whole-program denotation preservation for the right inclusion.** -/
theorem inr_denote {Γ : Ctxt e} {t : e.Ty} (c : Com e Γ t) :
    ComLowerTransports (inrLowering d e) inrTransTy inrMapVal c :=
  fundamental (inrLowering d e) inrTransTy inrMapVal
    inr_varTransports inr_opTransports inr_mapValExtends c

end Denote

/-! ## 7. A concrete coproduct

Two small dialects with different type alphabets: a numeric one whose single
type denotes to `Nat`, and a boolean one whose single type denotes to `Bool`.
Their coproduct hosts a program that uses an operation of each. -/

namespace Witness

/-- The type alphabet of the numeric dialect. -/
inductive NumTy where
  /-- The `Nat`-valued type. -/
  | num

/-- The operations of the numeric dialect. -/
inductive NumOp where
  /-- A `Nat` literal. -/
  | lit (n : Nat)
  /-- Addition of two `Nat`s. -/
  | add

/-- The type alphabet of the boolean dialect. -/
inductive FlagTy where
  /-- The `Bool`-valued type. -/
  | flag

/-- The operations of the boolean dialect. -/
inductive FlagOp where
  /-- A `Bool` literal. -/
  | lit (b : Bool)
  /-- Boolean negation. -/
  | neg

/-- A dialect of `Nat` literals and addition. -/
@[reducible] def numDialect : Dialect where
  Op := NumOp
  Ty := NumTy

/-- A dialect of `Bool` literals and negation. -/
@[reducible] def flagDialect : Dialect where
  Op := FlagOp
  Ty := FlagTy

instance : TyDenote NumTy where denote := fun _ => Nat

instance : TyDenote FlagTy where denote := fun _ => Bool

/-- The `Nat` carried by a value of the numeric dialect's type. Naming the
    value at `Nat` through a definition is what makes arithmetic instances
    available on it. -/
def natOf (x : ⟦NumTy.num⟧) : Nat := x

/-- The `Bool` carried by a value of the boolean dialect's type. -/
def boolOf (x : ⟦FlagTy.flag⟧) : Bool := x

instance : DialectSignature numDialect where
  sig
    | .lit _ => []
    | .add => [.num, .num]
  ret _ := .num

instance : DialectDenote numDialect where
  denote
    | .lit n => fun _ => n
    | .add => fun args => natOf args.head + natOf args.tail.head

instance : DialectSignature flagDialect where
  sig
    | .lit _ => []
    | .neg => [.flag]
  ret _ := .flag

instance : DialectDenote flagDialect where
  denote
    | .lit b => fun _ => b
    | .neg => fun args => !boolOf args.head

/-- The coproduct of the numeric and the boolean dialect. -/
@[reducible] def mixedDialect : Dialect := numDialect ⊕ flagDialect

instance : DialectSignature mixedDialect :=
  instDialectSignatureSum (d := numDialect) (e := flagDialect)

instance : DialectDenote mixedDialect :=
  instDialectDenoteSum (d := numDialect) (e := flagDialect)

/-- The numeric type inside the coproduct. -/
abbrev numT : mixedDialect.Ty := Sum.inl NumTy.num

/-- The boolean type inside the coproduct. -/
abbrev flagT : mixedDialect.Ty := Sum.inr FlagTy.flag

/-- A three-binding program over the coproduct:

    ```
    let a : inl num  = inl (lit 7)
    let b : inr flag = inr (lit true)
    let c : inl num  = inl (add a a)
    ret c
    ```

    The operations alternate between the summands, and `a` is read across the
    intervening `inr` binding. -/
def mixedProg : Com mixedDialect [] numT :=
  .var (t := numT) ⟨Sum.inl (NumOp.lit 7), rfl, .nil⟩
    (.var (t := flagT) ⟨Sum.inr (FlagOp.lit true), rfl, .nil⟩
      (.var (t := numT)
          ⟨Sum.inl NumOp.add, rfl, .cons (.there .here) (.cons (.there .here) .nil)⟩
        (.ret .here)))

/-- `mixedProg` denotes to `14`. -/
theorem mixedProg_denote : natOf (mixedProg.denote .nil) = 14 := rfl

/-- The same computation over the numeric dialect alone. -/
def numProg : Com numDialect [] NumTy.num :=
  .var ⟨NumOp.lit 7, rfl, .nil⟩
    (.var ⟨NumOp.add, rfl, .cons .here (.cons .here .nil)⟩ (.ret .here))

/-- `numProg` denotes to `14`. -/
theorem numProg_denote : natOf (numProg.denote .nil) = 14 := rfl

/-- The left inclusion's transport square at `numProg`. -/
theorem inl_numProg_transports :
    ComLowerTransports (inlLowering numDialect flagDialect) inlTransTy inlMapVal
      numProg :=
  inl_denote numProg

/-- `numProg` included into the coproduct denotes to `14`, read off the
    transport square rather than from the included program. -/
theorem inl_numProg_denote :
    natOf (((inlLowering numDialect flagDialect).lowerCom numProg).denote
      (inlMapVal .nil)) = 14 :=
  (congrArg natOf (inl_numProg_transports .nil)).trans numProg_denote

end Witness

end DialectCoproduct

end CatCrypt.Crypto.SecureCompilation.VIR
