/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgRel
public import CatCrypt.Crypto.SecureCompilation.VIR.PassChain

/-!
# Lane lifting of scalar structured programs into the tile level

`laneLift n w m rm p` maps a structured program `p : NFProg jasminDialect Γ ts` to a
program of `jasminTileDialect` that runs `n` copies of `p` in the lanes of tiles of `n`
lanes of `w` bits. The mask `m` marks the variables of `Γ` that hold lane data, and `rm`
the results that do: a marked variable of type `t` has the type `.inr (.tile n w)` in the
lifted program, an unmarked one the type `.inl t` (`liftTy`). An unmarked variable holds
the same value in every lane: trip counters, branch bits and public scalars.

The lifting is a recursion on the program along an environment `Env n w Γ Δ`, which gives
each source variable a scalar variable of the target context, a tile variable, or both.

* A `regArith`, `mulhi`, `shlImm`, `shrImm`, `sarImm` or `rorImm` at width `w` whose
  operands have tile variables becomes `tileBin`, `tileMulhu` or `tileShiftImm`.
* Every other operation whose operands all have scalar variables is kept in the scalar
  summand. A `regConst` at width `w` is bound twice, as the scalar constant and as
  `tileConst`, and its variable has both forms.
* A counted loop, a branch and an exit-flag loop map to the same constructor. The trip
  count and the branch bit are read at scalar variables, the carried tuple has the forms
  of its initial values (the scalar form where both exist), and a loop body returns the
  carried forms.
* A `call`, an operation with a tile operand and no tile counterpart, and an operation
  that mixes a tile operand with an operand that has no tile variable give `none`.

The lifting is defined for every scalar dialect `d` and every dialect `tileSide d O` over
the type alphabet of `d` beside the tile types, along a lane-operation table
`LaneTable d O n w`. The declarations at `jasminDialect` are the instance at the table
`jasminLane`.

## Main definitions

* `tileSide`, `LaneTable`, `LaneTable.Sound` — the tile-side dialect over a scalar dialect,
  a lane-operation table and its laws.
* `markTy`, `markTys`, `readMark`, `readMarks`, `LaneForms`, `LaneEnv`, `LaneRel` — the type
  map along a mask, the lane reading, and the environments, over a scalar dialect.
* `liftAlong`, `tableLift` — the lifting at a table, along an environment and at masks.
* `tableLiftCert`, `tableLiftLeakCert` — the step certificates of `tableLift` at lane `k`.
* `jasminLane` — the table of `jasminDialect`.
* `liftTy`, `liftTys` — the type map along a mask.
* `laneRd`, `outRd`, `laneOuts` — lane `k` of a tile, of a value and of a tuple.
* `LVar`, `Env`, `EnvRel` — the forms of a source variable in a target context, and the
  relation of a source valuation to a target valuation at lane `k`.
* `liftP`, `laneLift` — the lifting along an environment, and at entry and result masks.
* `LaneQuiet` — the leakage models in which the lifted scalar operations are quiet.
* `laneLiftCert`, `laneLiftLeakCert` — the step certificates at lane `k`.
* `accLoop` — the scalar counted loop with a carried accumulator.

## Main results

* `liftAlong_leakRun`, `tableLift_leakRun`, `tableLift_events`, `tableLift_denote` — for a
  table with its laws, the run of the lifted program read at lane `k` is the scalar run on
  lane `k`, with equal events.
* `jasminLane_sound` — the laws of `jasminLane`.
* `liftP_leakRun`, `laneLift_leakRun` — at every lane `k`, the run of the lifted program
  on a tile valuation and the run of the scalar program on lane `k` of that valuation
  both fail, or both succeed with lane `k` of the lifted results equal to the scalar
  results and with equal events.
* `laneLift_denote` — lane `k` of the lifted denotation is the scalar denotation on lane
  `k`, at every fuel.
* `laneLift_accLoop`, `accLoop_lane` — the lifting of `accLoop` is `tileAccLoop`, and the
  lane theorem at it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapNF

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

attribute [local instance] jasminTileDenote

/-! ## 1. Types and lanes -/

/-- The tile-side dialect over the scalar dialect `d` with the operations `O`: its type
    alphabet is that of `d` beside the tile types. -/
abbrev tileSide (d : Dialect.{0, 0}) (O : Type) : Dialect.{0, 0} where
  Op := O
  Ty := d.Ty ⊕ TileTy

/-- The trip counter of `tileSide d O` is the counter of `d`. -/
@[instance_reducible] def tileSideWord64 (d : Dialect.{0, 0}) [TyDenote d.Ty] [HasWord64 d]
    (O : Type) : HasWord64 (tileSide d O) where
  word := .inl (HasWord64.word (d := d))
  toNat := HasWord64.toNat (d := d)
  ofNat := HasWord64.ofNat (d := d)

/-- The bit of `tileSide d O` is the bit of `d`. -/
@[instance_reducible] def tileSideBoolBit (d : Dialect.{0, 0}) [TyDenote d.Ty] [HasBoolBit d]
    (O : Type) : HasBoolBit (tileSide d O) where
  bit := .inl (HasBitType.bit (d := d))
  toBool := HasBoolBit.toBool (d := d)

attribute [local instance] tileSideWord64 tileSideBoolBit

section Marks

variable {T : Type} (n w : Nat)

/-- The type of a variable of type `t` in a lifted program over the type alphabet `T`: the
    tile of `n` lanes of `w` bits when the variable is marked as lane data, the scalar type
    `t` otherwise. -/
def markTy (b : Bool) (t : T) : T ⊕ TileTy :=
  match b with
  | true => .inr (.tile n w)
  | false => .inl t

/-- The type list along a mask; a position past the end of the mask is scalar. -/
def markTys : List Bool → List T → List (T ⊕ TileTy)
  | _, [] => []
  | rm, t :: ts => markTy n w (rm.headD false) t :: markTys rm.tail ts

variable {n w} [TyDenote T]

/-- The scalar value of a marked value along the reading `r` of a tile: the reading of a
    tile, and the value of a scalar. -/
def readMark (r : (t : T) → (Fin n → BitVec w) → ⟦t⟧) (b : Bool) (t : T) :
    ⟦markTy n w b t⟧ → ⟦t⟧ :=
  match b with
  | true => fun x => r t x
  | false => fun x => x

/-- The scalar tuple of a marked tuple along the reading `r`. -/
def readMarks (r : (t : T) → (Fin n → BitVec w) → ⟦t⟧) : (rm : List Bool) → (ts : List T) →
    HVector (fun t => ⟦t⟧) (markTys n w rm ts) → HVector (fun t => ⟦t⟧) ts
  | _, [], _ => .nil
  | rm, t :: ts, .cons x xs =>
      .cons (readMark r (rm.headD false) t x) (readMarks r rm.tail ts xs)

/-- The scalar tuple of a non-empty marked tuple, by head and tail. -/
theorem readMarks_cons (r : (t : T) → (Fin n → BitVec w) → ⟦t⟧) (rm : List Bool) (t : T)
    (ts : List T) (o : HVector (fun t => ⟦t⟧) (markTys n w rm (t :: ts))) :
    readMarks r rm (t :: ts) o =
      .cons (readMark r (rm.headD false) t o.head) (readMarks r rm.tail ts o.tail) := by
  cases o
  rfl

end Marks

section Types

variable (n w : Nat)

/-- The type of a variable of type `t` in the lifted program: the tile of `n` lanes of
    `w` bits when the variable is marked as lane data, the scalar type `t` otherwise. -/
def liftTy (b : Bool) (t : JasminTy) : jasminTileDialect.Ty :=
  markTy n w b t

/-- The lifted type list along a mask; a position past the end of the mask is scalar. -/
def liftTys (rm : List Bool) (ts : List JasminTy) : List jasminTileDialect.Ty :=
  markTys n w rm ts

variable {n w}

/-- Lane `k` of a tile, read at the scalar type `t`: the lane at `reg w`, and the default
    value at every other type. -/
def laneRd (k : Fin n) : (t : JasminTy) → (Fin n → BitVec w) → ⟦t⟧
  | .reg w', x => if h : w' = w then (h ▸ x k : BitVec w') else (0 : BitVec w')
  | .stackArr w' _, _ => fun _ => (0 : BitVec w')
  | .inlineInt, _ => (0 : Nat)
  | .bool, _ => false

/-- Lane `k` of a tile at the lane type is the lane. -/
@[simp] theorem laneRd_reg (k : Fin n) (x : Fin n → BitVec w) : laneRd k (.reg w) x = x k := by
  simp [laneRd]

/-- Lane `k` of a lifted value: lane `k` of a tile, and the value of a scalar. -/
def outRd (k : Fin n) (b : Bool) (t : JasminTy) : ⟦liftTy n w b t⟧ → ⟦t⟧ :=
  readMark (laneRd k) b t

/-- Lane `k` of a lifted tuple. -/
def laneOuts (k : Fin n) (rm : List Bool) (ts : List JasminTy) :
    Valuation (d := jasminTileDialect) (liftTys n w rm ts) → Valuation (d := jasminDialect) ts :=
  readMarks (laneRd k) rm ts

/-- Lane `k` of a non-empty lifted tuple, by head and tail. -/
theorem laneOuts_cons (k : Fin n) (rm : List Bool) (t : JasminTy) (ts : List JasminTy)
    (o : Valuation (d := jasminTileDialect) (liftTys n w rm (t :: ts))) :
    laneOuts k rm (t :: ts) o =
      .cons (outRd k (rm.headD false) t o.head) (laneOuts k rm.tail ts o.tail) :=
  readMarks_cons (laneRd k) rm t ts o

end Types

/-! ## 2. Environments -/

section LaneEnvs

variable (d : Dialect.{0, 0}) (O : Type) (n w : Nat)

/-- The forms of a source variable of type `t` of the scalar dialect `d` in the context `Δ`
    of `tileSide d O`: a scalar variable, a tile variable, or both. -/
structure LaneForms (Δ : Ctxt (tileSide d O)) (t : d.Ty) where
  /-- The scalar form. -/
  sc : Option (Var Δ (Sum.inl t))
  /-- The tile form. -/
  ln : Option (Var Δ (Sum.inr (TileTy.tile n w)))

/-- An environment: the forms of every variable of `Γ` in `Δ`. -/
abbrev LaneEnv (Γ : Ctxt d) (Δ : Ctxt (tileSide d O)) : Type :=
  ∀ t : d.Ty, Var Γ t → LaneForms d O n w Δ t

variable {d O n w}

/-- The forms of a variable under one more binding of the target context. -/
def LaneForms.wk {Δ : Ctxt (tileSide d O)} {t : d.Ty} (u : (tileSide d O).Ty)
    (x : LaneForms d O n w Δ t) : LaneForms d O n w (u :: Δ) t :=
  ⟨x.sc.map .there, x.ln.map .there⟩

/-- The single form of a variable of the marked type `markTy n w b t`. -/
def LaneForms.ofTag {Δ : Ctxt (tileSide d O)} {t : d.Ty} (b : Bool) :
    Var Δ (markTy n w b t) → LaneForms d O n w Δ t :=
  match b with
  | true => fun v => ⟨none, some v⟩
  | false => fun v => ⟨some v, none⟩

/-- The form of a variable at a region boundary: the scalar form when it exists, the tile
    form otherwise. -/
def LaneForms.pick {Δ : Ctxt (tileSide d O)} {t : d.Ty} (x : LaneForms d O n w Δ t) :
    Option ((b : Bool) × Var Δ (markTy n w b t)) :=
  match x.sc, x.ln with
  | some v, _ => some ⟨false, v⟩
  | none, some v => some ⟨true, v⟩
  | none, none => none

/-- The environment under a binding of the form `b`. -/
def LaneEnv.cons {Γ : Ctxt d} {Δ : Ctxt (tileSide d O)} (ρ : LaneEnv d O n w Γ Δ)
    (b : Bool) {t : d.Ty} : LaneEnv d O n w (t :: Γ) (markTy n w b t :: Δ)
  | _, .here => LaneForms.ofTag b .here
  | _, .there v => (ρ _ v).wk _

/-- The environment under a binding with both forms: the tile variable is bound last. -/
def LaneEnv.cons2 {Γ : Ctxt d} {Δ : Ctxt (tileSide d O)} (ρ : LaneEnv d O n w Γ Δ)
    {t : d.Ty} : LaneEnv d O n w (t :: Γ) (Sum.inr (TileTy.tile n w) :: Sum.inl t :: Δ)
  | _, .here => ⟨some (.there .here), some .here⟩
  | _, .there v => ((ρ _ v).wk _).wk _

/-- The environment under a tuple of bindings of the forms `rm`. -/
def LaneEnv.app {Γ : Ctxt d} {Δ : Ctxt (tileSide d O)} (ρ : LaneEnv d O n w Γ Δ) :
    (rm : List Bool) → (cs : List d.Ty) → LaneEnv d O n w (cs ++ Γ) (markTys n w rm cs ++ Δ)
  | _, [] => ρ
  | rm, _ :: cs => (LaneEnv.app ρ rm.tail cs).cons (rm.headD false)

/-- The environment of the marked context along the mask `m`. -/
def LaneEnv.ofMask : (m : List Bool) → (Γ : Ctxt d) → LaneEnv d O n w Γ (markTys n w m Γ)
  | _, [] => fun _ v => nomatch v
  | m, _ :: Γ => (LaneEnv.ofMask m.tail Γ).cons (m.headD false)

variable [TyDenote d.Ty]

/-- A source valuation `V` is the reading `r` of the target valuation `W` along `ρ`: a
    scalar form reads the source value, and the reading of a tile form is the source
    value. -/
def LaneRel (r : (t : d.Ty) → (Fin n → BitVec w) → ⟦t⟧) {Γ : Ctxt d}
    {Δ : Ctxt (tileSide d O)} (ρ : LaneEnv d O n w Γ Δ) (V : Valuation Γ) (W : Valuation Δ) :
    Prop :=
  ∀ (t : d.Ty) (v : Var Γ t),
    (∀ v', (ρ t v).sc = some v' → v'.lookup W = v.lookup V) ∧
    (∀ v', (ρ t v).ln = some v' → r t (v'.lookup W) = v.lookup V)

variable {r : (t : d.Ty) → (Fin n → BitVec w) → ⟦t⟧}

theorem LaneRel.cons {Γ : Ctxt d} {Δ : Ctxt (tileSide d O)} {ρ : LaneEnv d O n w Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (hρ : LaneRel r ρ V W) (b : Bool) {t : d.Ty}
    (x' : ⟦markTy n w b t⟧) (x : ⟦t⟧) (hx : readMark r b t x' = x) :
    LaneRel r (ρ.cons b (t := t)) (V.extend x) (W.extend x') := by
  intro t' v
  cases v with
  | here =>
      cases b
      · exact ⟨fun v' hv => by cases hv; exact hx, fun v' hv => nomatch hv⟩
      · exact ⟨fun v' hv => (nomatch hv), fun v' hv => by cases hv; exact hx⟩
  | there v =>
      refine ⟨fun v' hv => ?_, fun v' hv => ?_⟩
      · obtain ⟨v0, h0, rfl⟩ := Option.map_eq_some_iff.mp hv
        exact (hρ _ v).1 v0 h0
      · obtain ⟨v0, h0, rfl⟩ := Option.map_eq_some_iff.mp hv
        exact (hρ _ v).2 v0 h0

theorem LaneRel.cons2 {Γ : Ctxt d} {Δ : Ctxt (tileSide d O)} {ρ : LaneEnv d O n w Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (hρ : LaneRel r ρ V W) {t : d.Ty} (x : ⟦t⟧)
    (xt : Fin n → BitVec w) (hx : r t xt = x) :
    LaneRel r (ρ.cons2 (t := t)) (V.extend x)
      (Valuation.extend (d := tileSide d O) (t := Sum.inr (TileTy.tile n w))
        (Valuation.extend (d := tileSide d O) (t := Sum.inl t) W x) xt) := by
  intro t' v
  cases v with
  | here =>
      exact ⟨fun v' hv => by cases hv; rfl, fun v' hv => by cases hv; exact hx⟩
  | there v =>
      refine ⟨fun v' hv => ?_, fun v' hv => ?_⟩
      · obtain ⟨v1, h1, rfl⟩ := Option.map_eq_some_iff.mp hv
        obtain ⟨v0, h0, rfl⟩ := Option.map_eq_some_iff.mp h1
        exact (hρ _ v).1 v0 h0
      · obtain ⟨v1, h1, rfl⟩ := Option.map_eq_some_iff.mp hv
        obtain ⟨v0, h0, rfl⟩ := Option.map_eq_some_iff.mp h1
        exact (hρ _ v).2 v0 h0

theorem LaneRel.app {Γ : Ctxt d} {Δ : Ctxt (tileSide d O)} {ρ : LaneEnv d O n w Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (hρ : LaneRel r ρ V W) :
    (rm : List Bool) → (cs : List d.Ty) →
    (a : Valuation (d := tileSide d O) (markTys n w rm cs)) →
    LaneRel r (ρ.app rm cs) (hvAppend (readMarks r rm cs a) V) (hvAppend a W)
  | _, [], .nil => hρ
  | rm, _ :: cs, .cons x xs =>
      LaneRel.cons (LaneRel.app hρ rm.tail cs xs) (rm.headD false) x _ rfl

theorem LaneRel.ofMask (r : (t : d.Ty) → (Fin n → BitVec w) → ⟦t⟧) :
    (m : List Bool) → (Γ : Ctxt d) → (W : Valuation (d := tileSide d O) (markTys n w m Γ)) →
    LaneRel r (LaneEnv.ofMask m Γ) (readMarks r m Γ W) W
  | _, [], _ => fun _ v => nomatch v
  | m, _ :: Γ, .cons x xs =>
      LaneRel.cons (LaneRel.ofMask r m.tail Γ xs) (m.headD false) x _ rfl

end LaneEnvs

section Envs

variable (n w : Nat)

/-- The forms of a source variable of type `t` in the target context `Δ`: a scalar
    variable, a tile variable, or both. -/
abbrev LVar (Δ : Ctxt jasminTileDialect) (t : JasminTy) : Type :=
  LaneForms jasminDialect (Sum JasminOp TileOp) n w Δ t

/-- An environment: the forms of every variable of `Γ` in `Δ`. -/
abbrev Env (Γ : Ctxt jasminDialect) (Δ : Ctxt jasminTileDialect) : Type :=
  ∀ t : JasminTy, Var Γ t → LVar n w Δ t

variable {n w}

/-- The forms of a variable under one more binding of the target context. -/
def LVar.wk {Δ : Ctxt jasminTileDialect} {t : JasminTy} (u : jasminTileDialect.Ty)
    (x : LVar n w Δ t) : LVar n w (u :: Δ) t :=
  LaneForms.wk (d := jasminDialect) (O := Sum JasminOp TileOp) u x

/-- The single form of a variable of the lifted type `liftTy n w b t`. -/
def LVar.ofTag {Δ : Ctxt jasminTileDialect} {t : JasminTy} (b : Bool) :
    Var Δ (liftTy n w b t) → LVar n w Δ t :=
  LaneForms.ofTag (d := jasminDialect) (O := Sum JasminOp TileOp) b

/-- The form of a variable at a region boundary: the scalar form when it exists, the tile
    form otherwise. -/
def LVar.pick {Δ : Ctxt jasminTileDialect} {t : JasminTy} (x : LVar n w Δ t) :
    Option ((b : Bool) × Var Δ (liftTy n w b t)) :=
  LaneForms.pick (d := jasminDialect) (O := Sum JasminOp TileOp) x

/-- The environment under a binding of the form `b`. -/
def Env.cons {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} (ρ : Env n w Γ Δ)
    (b : Bool) {t : JasminTy} : Env n w (t :: Γ) (liftTy n w b t :: Δ) :=
  LaneEnv.cons (d := jasminDialect) (O := Sum JasminOp TileOp) ρ b

/-- The environment under a binding with both forms: the tile variable is bound last. -/
def Env.cons2 {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} (ρ : Env n w Γ Δ)
    {t : JasminTy} : Env n w (t :: Γ) (Sum.inr (TileTy.tile n w) :: Sum.inl t :: Δ) :=
  LaneEnv.cons2 (d := jasminDialect) (O := Sum JasminOp TileOp) ρ

/-- The environment under a tuple of bindings of the forms `rm`. -/
def Env.app {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} (ρ : Env n w Γ Δ)
    (rm : List Bool) (cs : List JasminTy) : Env n w (cs ++ Γ) (liftTys n w rm cs ++ Δ) :=
  LaneEnv.app (d := jasminDialect) (O := Sum JasminOp TileOp) ρ rm cs

/-- The environment of the lifted context along the mask `m`. -/
def Env.ofMask (m : List Bool) (Γ : Ctxt jasminDialect) : Env n w Γ (liftTys n w m Γ) :=
  LaneEnv.ofMask (d := jasminDialect) (O := Sum JasminOp TileOp) m Γ

/-- A source valuation `V` is lane `k` of the target valuation `W` along `ρ`: a scalar
    form reads the source value, and lane `k` of a tile form is the source value. -/
def EnvRel (k : Fin n) {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect}
    (ρ : Env n w Γ Δ) (V : Valuation Γ) (W : Valuation Δ) : Prop :=
  LaneRel (laneRd k) ρ V W

theorem EnvRel.cons {k : Fin n} {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect}
    {ρ : Env n w Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (hρ : EnvRel k ρ V W) (b : Bool)
    {t : JasminTy} (x' : ⟦liftTy n w b t⟧) (x : ⟦t⟧) (hx : outRd k b t x' = x) :
    EnvRel k (ρ.cons b (t := t)) (V.extend x) (W.extend x') :=
  LaneRel.cons hρ b x' x hx

theorem EnvRel.cons2 {k : Fin n} {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect}
    {ρ : Env n w Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (hρ : EnvRel k ρ V W)
    {t : JasminTy} (x : ⟦t⟧) (xt : Fin n → BitVec w) (hx : laneRd k t xt = x) :
    EnvRel k (ρ.cons2 (t := t)) (V.extend x)
      (Valuation.extend (d := jasminTileDialect) (t := Sum.inr (TileTy.tile n w))
        (Valuation.extend (d := jasminTileDialect) (t := Sum.inl t) W x) xt) :=
  LaneRel.cons2 hρ x xt hx

theorem EnvRel.app {k : Fin n} {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect}
    {ρ : Env n w Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (hρ : EnvRel k ρ V W)
    (rm : List Bool) (cs : List JasminTy)
    (a : Valuation (d := jasminTileDialect) (liftTys n w rm cs)) :
    EnvRel k (ρ.app rm cs) (hvAppend (laneOuts k rm cs a) V) (hvAppend a W) :=
  LaneRel.app hρ rm cs a

theorem EnvRel.ofMask (k : Fin n) (m : List Bool) (Γ : Ctxt jasminDialect)
    (W : Valuation (d := jasminTileDialect) (liftTys n w m Γ)) :
    EnvRel k (Env.ofMask m Γ) (laneOuts k m Γ W) W :=
  LaneRel.ofMask (d := jasminDialect) (O := Sum JasminOp TileOp) (laneRd k) m Γ W

end Envs

/-! ## 3. The lifting -/

section LaneLift

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [HasWord64 d]
  [HasBoolBit d] {O : Type} [DialectSignature (tileSide d O)] {n w : Nat}

omit [TyDenote d.Ty] [DialectSignature d] [HasWord64 d] [HasBoolBit d]
  [DialectSignature (tileSide d O)] in
/-- The variables of a region boundary in the forms `LaneForms.pick` chooses, with the mask
    of those forms. -/
def boundaryArgs {Γ : Ctxt d} {Δ : Ctxt (tileSide d O)} (ρ : LaneEnv d O n w Γ Δ) :
    {ts : List d.Ty} → HVector (fun t => Var Γ t) ts →
    Option ((rm : List Bool) × HVector (fun t => Var Δ t) (markTys n w rm ts))
  | [], .nil => some ⟨[], .nil⟩
  | _ :: _, .cons v vs =>
      (ρ _ v).pick.bind fun bv =>
        (boundaryArgs ρ vs).map fun r => ⟨bv.1 :: r.1, .cons bv.2 r.2⟩

omit [TyDenote d.Ty] [DialectSignature d] [HasWord64 d] [HasBoolBit d]
  [DialectSignature (tileSide d O)] in
/-- The scalar forms of an argument vector, when every argument has one. -/
def scalarArgs {Γ : Ctxt d} {Δ : Ctxt (tileSide d O)} (ρ : LaneEnv d O n w Γ Δ) :
    {ts : List d.Ty} → HVector (fun t => Var Γ t) ts →
    Option (HVector (fun t => Var Δ t) (ts.map (Sum.inl (β := TileTy))))
  | [], .nil => some .nil
  | _ :: _, .cons v vs => (ρ _ v).sc.bind fun v' => (scalarArgs ρ vs).map (.cons v')

variable (d O n w) in
/-- **A lane-operation table** of the scalar dialect `d` into `tileSide d O` at `n` lanes of
    `w` bits: the reading of a lane of a tile at each scalar type, the scalar operations with
    a tile counterpart, the tile expression of such an operation on operands with tile
    forms, the constant operations and the tile constant, and the expression that keeps a
    scalar operation on operands with scalar forms. -/
structure LaneTable where
  /-- Lane `k` of a tile, read at the scalar type `t`. -/
  rd : Fin n → (t : d.Ty) → (Fin n → BitVec w) → ⟦t⟧
  /-- The scalar operations with a tile counterpart. -/
  isLane : d.Op → Bool
  /-- The tile expression of a scalar operation whose operands have tile forms. -/
  tile : {Γ : Ctxt d} → {Δ : Ctxt (tileSide d O)} → LaneEnv d O n w Γ Δ → (op : d.Op) →
    HVector (fun t => Var Γ t) (DialectSignature.sig op) →
    Option (Expr (tileSide d O) Δ (Sum.inr (TileTy.tile n w)))
  /-- The value of a constant operation at the lane width. -/
  const : d.Op → Option Nat
  /-- The tile with every lane equal to a constant. -/
  constE : Nat → {Δ : Ctxt (tileSide d O)} →
    Expr (tileSide d O) Δ (Sum.inr (TileTy.tile n w))
  /-- A scalar operation on scalar forms as an expression of the tile side; `none` where
      the tile side has no such operation. -/
  keep : (op : d.Op) → {t : d.Ty} → DialectSignature.ret op = t →
    {Δ : Ctxt (tileSide d O)} →
    HVector (fun u => Var Δ u) ((DialectSignature.sig op).map (Sum.inl (β := TileTy))) →
    Option (Expr (tileSide d O) Δ (Sum.inl t))

omit [TyDenote d.Ty] [DialectSignature d] in
/-- A lifted program with its result mask carried along an equality of masks. -/
def castMask {Δ : Ctxt (tileSide d O)} {ts : List d.Ty} {rm rm' : List Bool} (h : rm = rm')
    (q : NFProg (tileSide d O) Δ (markTys n w rm ts)) :
    NFProg (tileSide d O) Δ (markTys n w rm' ts) :=
  h ▸ q

/-- **The lifting along an environment** at the table `L`. The result is the mask of the
    forms of the returned variables and the lifted program; `none` where the program is
    refused. -/
def liftAlong (L : LaneTable d O n w) : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts →
    {Δ : Ctxt (tileSide d O)} → LaneEnv d O n w Γ Δ →
    Option ((rm : List Bool) × NFProg (tileSide d O) Δ (markTys n w rm ts))
  | _, _, .ret vs, _, ρ => (boundaryArgs ρ vs).map fun r => ⟨r.1, .ret r.2⟩
  | _, _, .var e k, _, ρ =>
      match L.tile ρ e.op e.args with
      | some e' => (liftAlong L k (ρ.cons true)).map fun r => ⟨r.1, .var e' r.2⟩
      | none =>
          (scalarArgs ρ e.args).bind fun as =>
            (L.keep e.op e.retTy_eq as).bind fun e₀ =>
              match L.const e.op with
              | some c =>
                  (liftAlong L k ρ.cons2).map fun r => ⟨r.1, .var e₀ (.var (L.constE c) r.2)⟩
              | none =>
                  (liftAlong L k (ρ.cons false)).map fun r => ⟨r.1, .var e₀ r.2⟩
  | _, _, .forLoop (cs := cs) count inits body k, _, ρ =>
      (ρ _ count).sc.bind fun c' =>
        (boundaryArgs ρ inits).bind fun ri =>
          (liftAlong L body (LaneEnv.app (ρ.cons false) ri.1 cs)).bind fun rb =>
            if h : rb.1 = ri.1 then
              (liftAlong L k (LaneEnv.app ρ ri.1 cs)).map fun rk =>
                ⟨rk.1, .forLoop c' ri.2 (castMask h rb.2) rk.2⟩
            else none
  | _, _, .ifThenElse (rs := rs) cond thn els k, _, ρ =>
      (ρ _ cond).sc.bind fun c' =>
        (liftAlong L thn ρ).bind fun rt =>
          (liftAlong L els ρ).bind fun re =>
            if h : re.1 = rt.1 then
              (liftAlong L k (LaneEnv.app ρ rt.1 rs)).map fun rk =>
                ⟨rk.1, .ifThenElse c' rt.2 (castMask h re.2) rk.2⟩
            else none
  | _, _, .whileLoop (cs := cs) inits body k, _, ρ =>
      (boundaryArgs ρ inits).bind fun ri =>
        (liftAlong L body (LaneEnv.app ρ ri.1 cs)).bind fun rb =>
          if h : rb.1 = false :: ri.1 then
            (liftAlong L k (LaneEnv.app ρ ri.1 cs)).map fun rk =>
              ⟨rk.1, .whileLoop ri.2 (castMask h rb.2) rk.2⟩
          else none
  | _, _, .call .., _, _ => none

/-- **Lane lifting at the table `L`.** The lifting of `p` at the entry mask `m`, when the
    forms of its results are those of the mask `rm`. -/
def tableLift (L : LaneTable d O n w) (m rm : List Bool) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) : Option (NFProg (tileSide d O) (markTys n w m Γ) (markTys n w rm ts)) :=
  (liftAlong L p (LaneEnv.ofMask m Γ)).bind fun r =>
    if h : r.1 = rm then some (castMask h r.2) else none

end LaneLift

section Lift

variable (n w : Nat)

/-- The variables of a region boundary in the forms `LVar.pick` chooses, with the mask of
    those forms. -/
def retArgs {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} (ρ : Env n w Γ Δ)
    {ts : List JasminTy} (vs : HVector (fun t => Var Γ t) ts) :
    Option ((rm : List Bool) × HVector (fun t => Var Δ t) (liftTys n w rm ts)) :=
  boundaryArgs (d := jasminDialect) (O := Sum JasminOp TileOp) ρ vs

/-- The scalar forms of an argument vector, when every argument has one. -/
def scArgs {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} (ρ : Env n w Γ Δ)
    {ts : List JasminTy} (vs : HVector (fun t => Var Γ t) ts) :
    Option (HVector (fun t => Var Δ t) (ts.map (Sum.inl (β := TileTy)))) :=
  scalarArgs (d := jasminDialect) (O := Sum JasminOp TileOp) ρ vs

/-- The scalar operations with a tile counterpart at lane width `w`. -/
def isLaneOp : JasminOp → Bool
  | .regArith _ w' => decide (w' = w)
  | .mulhi w' => decide (w' = w)
  | .shlImm w' _ => decide (w' = w)
  | .shrImm w' _ => decide (w' = w)
  | .sarImm w' _ => decide (w' = w)
  | .rorImm w' _ => decide (w' = w)
  | _ => false

/-- The tile expression of a scalar operation at width `w` whose operands have tile
    forms. -/
def tileOp? {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} (ρ : Env n w Γ Δ) :
    (op : JasminOp) → HVector (fun t => Var Γ t) (DialectSignature.sig op) →
    Option (Expr jasminTileDialect Δ (Sum.inr (TileTy.tile n w)))
  | .regArith bop w', args =>
      if w' = w then
        (ρ _ args.head).ln.bind fun a => (ρ _ args.tail.head).ln.map fun b =>
          ⟨.inr (.tileBin bop n w), rfl, .cons a (.cons b .nil)⟩
      else none
  | .mulhi w', args =>
      if w' = w then
        (ρ _ args.head).ln.bind fun a => (ρ _ args.tail.head).ln.map fun b =>
          ⟨.inr (.tileMulhu n w), rfl, .cons a (.cons b .nil)⟩
      else none
  | .shlImm w' c, args =>
      if w' = w then
        (ρ _ args.head).ln.map fun a => ⟨.inr (.tileShiftImm .shl n w c), rfl, .cons a .nil⟩
      else none
  | .shrImm w' c, args =>
      if w' = w then
        (ρ _ args.head).ln.map fun a => ⟨.inr (.tileShiftImm .lshr n w c), rfl, .cons a .nil⟩
      else none
  | .sarImm w' c, args =>
      if w' = w then
        (ρ _ args.head).ln.map fun a => ⟨.inr (.tileShiftImm .ashr n w c), rfl, .cons a .nil⟩
      else none
  | .rorImm w' c, args =>
      if w' = w then
        (ρ _ args.head).ln.map fun a => ⟨.inr (.tileShiftImm .rotr n w c), rfl, .cons a .nil⟩
      else none
  | _, _ => none

/-- The value of a constant operation at width `w`. -/
def constOf? : JasminOp → Option Nat
  | .regConst w' c => if w' = w then some c else none
  | _ => none

/-- A lifted program with its result mask carried along an equality of masks. -/
def castRes {Δ : Ctxt jasminTileDialect} {ts : List JasminTy} {rm rm' : List Bool}
    (h : rm = rm') (q : NFProg jasminTileDialect Δ (liftTys n w rm ts)) :
    NFProg jasminTileDialect Δ (liftTys n w rm' ts) :=
  castMask (d := jasminDialect) (O := Sum JasminOp TileOp) h q

/-- **The lane-operation table of `jasminDialect`** into `jasminTileDialect`: the lane
    reading `laneRd`, the operations `isLaneOp`, their tile expressions `tileOp?`, the
    constants `constOf?` with `tileConst`, and every scalar operation kept in the scalar
    summand. -/
@[reducible] def jasminLane : LaneTable jasminDialect (Sum JasminOp TileOp) n w where
  rd := laneRd
  isLane := isLaneOp w
  tile := tileOp? n w
  const := constOf? w
  constE := fun c => ⟨.inr (.tileConst n w c), rfl, .nil⟩
  keep := fun op _ h _ as => some ⟨.inl op, congrArg Sum.inl h, as⟩

/-- **The lifting along an environment.** The result is the mask of the forms of the
    returned variables and the lifted program; `none` where the program is refused. -/
def liftP {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    {Δ : Ctxt jasminTileDialect} (ρ : Env n w Γ Δ) :
    Option ((rm : List Bool) × NFProg jasminTileDialect Δ (liftTys n w rm ts)) :=
  liftAlong (jasminLane n w) p ρ

/-- **Lane lifting.** The lifting of `p` at the entry mask `m`, when the forms of its
    results are those of the mask `rm`. -/
def laneLift (m rm : List Bool) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    Option (NFProg jasminTileDialect (liftTys n w m Γ) (liftTys n w rm ts)) :=
  tableLift (jasminLane n w) m rm p

end Lift

/-! ## 4. Preservation of results and events -/

section Sound

variable {n w : Nat}

theorem rel_mono {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b)
    {o : Option α} {o' : Option β} (ho : Option.Rel R o o') : Option.Rel S o o' := by
  cases ho with
  | none => exact .none
  | some hr => exact .some (h _ _ hr)

theorem rel_map_ev {A A' : Type} {R : A → A' → Prop} (f : List CTLeak → List CTLeak)
    {o : Option (A × List CTLeak)} {o' : Option (A' × List CTLeak)}
    (h : Option.Rel (fun r r' => R r.1 r'.1 ∧ r.2 = r'.2) o o') :
    Option.Rel (fun r r' => R r.1 r'.1 ∧ r.2 = r'.2)
      (o.map fun r => (r.1, f r.2)) (o'.map fun r => (r.1, f r.2)) := by
  cases h with
  | none => exact .none
  | some hr => exact .some ⟨hr.1, by simp only [hr.2]⟩

theorem rel_bind_map {A A' B B' : Type} {RA : A → A' → Prop} {RB : B → B' → Prop}
    (f : List CTLeak → List CTLeak → List CTLeak)
    {o : Option (A × List CTLeak)} {o' : Option (A' × List CTLeak)}
    {c : A → Option (B × List CTLeak)} {c' : A' → Option (B' × List CTLeak)}
    (ho : Option.Rel (fun r r' => RA r.1 r'.1 ∧ r.2 = r'.2) o o')
    (hc : ∀ a a', RA a a' → Option.Rel (fun r r' => RB r.1 r'.1 ∧ r.2 = r'.2) (c a) (c' a')) :
    Option.Rel (fun r r' => RB r.1 r'.1 ∧ r.2 = r'.2)
      (o.bind fun r => (c r.1).map fun q => (q.1, f r.2 q.2))
      (o'.bind fun r => (c' r.1).map fun q => (q.1, f r.2 q.2)) := by
  cases ho with
  | none => exact .none
  | some hr =>
      obtain ⟨h1, h2⟩ := hr
      simp only [Option.bind_some]
      rw [h2]
      exact rel_map_ev _ (hc _ _ h1)

theorem rel_snd {A A' : Type} {R : A → A' → Prop} {o : Option (A × List CTLeak)}
    {o' : Option (A' × List CTLeak)}
    (h : Option.Rel (fun r r' => R r.1 r'.1 ∧ r.2 = r'.2) o o') :
    o'.map Prod.snd = o.map Prod.snd := by
  cases h with
  | none => rfl
  | some hr => exact congrArg some hr.2.symm

theorem rel_fst {A A' : Type} {T : A' → A} {o : Option (A × List CTLeak)}
    {o' : Option (A' × List CTLeak)}
    (h : Option.Rel (fun r r' => r.1 = T r'.1 ∧ r.2 = r'.2) o o') :
    (o'.map Prod.fst).map T = o.map Prod.fst := by
  cases h with
  | none => rfl
  | some hr => exact congrArg some hr.1.symm

section LaneSound

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [HasWord64 d]
  [HasBoolBit d] {O : Type} [DialectSignature (tileSide d O)]
  {r : (t : d.Ty) → (Fin n → BitVec w) → ⟦t⟧}
  {Γ : Ctxt d} {Δ : Ctxt (tileSide d O)} {ρ : LaneEnv d O n w Γ Δ}
  {V : Valuation Γ} {W : Valuation Δ}

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectSignature (tileSide d O)] in
theorem LaneForms.pick_sound (hρ : LaneRel r ρ V W) {t : d.Ty} (v : Var Γ t)
    {bv : (b : Bool) × Var Δ (markTy n w b t)} (h : (ρ t v).pick = some bv) :
    readMark r bv.1 t (bv.2.lookup W) = v.lookup V := by
  unfold LaneForms.pick at h
  split at h
  · cases h
    exact (hρ t v).1 _ ‹_›
  · cases h
    exact (hρ t v).2 _ ‹_›
  · cases h

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectSignature (tileSide d O)] in
theorem boundaryArgs_sound (hρ : LaneRel r ρ V W) : {ts : List d.Ty} →
    (vs : HVector (fun t => Var Γ t) ts) →
    (a : (rm : List Bool) × HVector (fun t => Var Δ t) (markTys n w rm ts)) →
    boundaryArgs ρ vs = some a →
    Expr.lookupArgs vs V = readMarks r a.1 ts (Expr.lookupArgs a.2 W)
  | [], .nil, a, h => by cases h; rfl
  | _ :: _, .cons v vs, a, h => by
      obtain ⟨bv, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
      exact congrArg₂ HVector.cons (LaneForms.pick_sound hρ v hb).symm
        (boundaryArgs_sound hρ vs a' ha)

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectSignature (tileSide d O)] in
theorem scalarArgs_sound (hρ : LaneRel r ρ V W) : {ts : List d.Ty} →
    (vs : HVector (fun t => Var Γ t) ts) →
    (as : HVector (fun t => Var Δ t) (ts.map (Sum.inl (β := TileTy)))) →
    scalarArgs ρ vs = some as →
    unmapInl (d := d) (e := tileDialect) (Expr.lookupArgs as W) = Expr.lookupArgs vs V
  | [], .nil, _, _ => rfl
  | _ :: _, .cons v vs, as, h => by
      obtain ⟨v', hv, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨as', ha, rfl⟩ := Option.map_eq_some_iff.mp h
      exact congrArg₂ HVector.cons ((hρ _ v).1 v' hv) (scalarArgs_sound hρ vs as' ha)

variable [DialectDenoteM d Option] [DialectDenoteM (tileSide d O) Option]

/-- **The laws of a lane-operation table** for the leakage models `M` of `d` and `MT` of
    `tileSide d O`. A tile expression of the table succeeds without events, and each lane of
    its value is the value of the scalar operation on that lane of the operands; a constant
    operation returns the constant in every lane, and the tile constant is that tile; a kept
    operation has the value and the events of the scalar operation. -/
structure LaneTable.Sound (L : LaneTable d O n w) (M : LeakModel d)
    (MT : LeakModel (tileSide d O)) : Prop where
  /-- A tile expression succeeds without events, lane by lane as the scalar operation. -/
  tile : ∀ {Γ : Ctxt d} {Δ : Ctxt (tileSide d O)} {ρ : LaneEnv d O n w Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} {j : Fin n}, LaneRel (L.rd j) ρ V W →
    ∀ (op : d.Op) (args : HVector (fun t => Var Γ t) (DialectSignature.sig op))
      (e' : Expr (tileSide d O) Δ (Sum.inr (TileTy.tile n w))),
      L.tile ρ op args = some e' →
      L.isLane op = true ∧ ∃ x' : Fin n → BitVec w,
        e'.denoteM (M := Option) W = some x' ∧
        DialectDenoteM.denoteM (M := Option) op (Expr.lookupArgs args V) =
          some (L.rd j (DialectSignature.ret op) x') ∧
        Expr.ctLeak MT e' W = []
  /-- A constant operation returns the constant of the table in every lane. -/
  const : ∀ (j : Fin n) (op : d.Op) (c : Nat), L.const op = some c →
    ∀ (vals : HVector (fun t : d.Ty => ⟦t⟧) (DialectSignature.sig op))
      (x : ⟦DialectSignature.ret op⟧),
      DialectDenoteM.denoteM (M := Option) op vals = some x →
      L.rd j (DialectSignature.ret op) (tileConstApply n w c) = x
  /-- The tile constant is the tile with every lane equal to the constant. -/
  constE_denote : ∀ (c : Nat) {Δ : Ctxt (tileSide d O)} (W : Valuation Δ),
    (L.constE c (Δ := Δ)).denoteM (M := Option) W = some (tileConstApply n w c)
  /-- The tile constant emits no event. -/
  constE_leak : ∀ (c : Nat) {Δ : Ctxt (tileSide d O)} (W : Valuation Δ),
    Expr.ctLeak MT (L.constE c (Δ := Δ)) W = []
  /-- A kept operation has the value and the events of the scalar operation. -/
  keep : ∀ (op : d.Op) {Δ : Ctxt (tileSide d O)}
    (as : HVector (fun u => Var Δ u) ((DialectSignature.sig op).map (Sum.inl (β := TileTy))))
    (e' : Expr (tileSide d O) Δ (Sum.inl (DialectSignature.ret op))) (W : Valuation Δ),
    L.keep op rfl as = some e' →
    e'.denoteM (M := Option) W =
        DialectDenoteM.denoteM (M := Option) op
          (unmapInl (d := d) (e := tileDialect) (Expr.lookupArgs as W)) ∧
      Expr.ctLeak MT e' W =
        opLeak M op (unmapInl (d := d) (e := tileDialect) (Expr.lookupArgs as W))

/-- **The lifting at a table preserves runs at every lane.** For a table `L` with its laws
    at `M` and `MT`, a model `M` in which the operations of the table are quiet, a program
    `liftAlong L` accepts along `ρ`, and valuations related at lane `j`: the scalar run and
    the lifted run both fail, or both succeed with lane `j` of the lifted results equal to
    the scalar results and equal events. -/
theorem liftAlong_leakRun (L : LaneTable d O n w) (M : LeakModel d)
    (MT : LeakModel (tileSide d O)) (hL : L.Sound M MT)
    (hM : ∀ op, L.isLane op = true → M.kind op = .quiet) (fuel : Nat) (j : Fin n)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt (tileSide d O)} (ρ : LaneEnv d O n w Γ Δ)
      (a : (rm : List Bool) × NFProg (tileSide d O) Δ (markTys n w rm ts)),
      liftAlong L p ρ = some a → ∀ (V : Valuation Γ) (W : Valuation Δ),
      LaneRel (L.rd j) ρ V W →
      Option.Rel (fun b b' => b.1 = readMarks (L.rd j) a.1 ts b'.1 ∧ b.2 = b'.2)
        (NFProg.leakRunM M fuel p V) (NFProg.leakRunM MT fuel a.2 W) := by
  induction p with
  | ret vs =>
      intro Δ ρ a hr V W hρ
      obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp hr
      exact .some ⟨boundaryArgs_sound hρ vs r' h', rfl⟩
  | var e k ih =>
      intro Δ ρ a hr V W hρ
      obtain ⟨op, rfl, args⟩ := e
      simp only [liftAlong] at hr
      split at hr
      · rename_i e' he
        obtain ⟨rk, hk, rfl⟩ := Option.map_eq_some_iff.mp hr
        obtain ⟨hl, x', hx', hsd, hleak⟩ := hL.tile hρ op args e' he
        have hsrc : Expr.ctLeak M (⟨op, rfl, args⟩ : Expr d _ _) V = [] := by
          unfold Expr.ctLeak opLeak
          rw [hM _ hl]
        have hsd' : Expr.denoteM (M := Option) (⟨op, rfl, args⟩ : Expr d _ _) V =
            some (L.rd j (DialectSignature.ret op) x') := hsd
        simp only [NFProg.leakRunM, Option.bind_some, hx', hleak, hsrc, hsd']
        exact rel_map_ev (R := fun b b' => b = readMarks (L.rd j) rk.1 _ b') _
          (ih _ rk hk _ _ (hρ.cons true x' _ rfl))
      · obtain ⟨as, has, hr⟩ := Option.bind_eq_some_iff.mp hr
        obtain ⟨e₀, he₀, hr⟩ := Option.bind_eq_some_iff.mp hr
        have hargs := scalarArgs_sound hρ args as has
        obtain ⟨hden₀, hlk₀⟩ := hL.keep op as e₀ W he₀
        rw [hargs] at hden₀ hlk₀
        have hden : Expr.denoteM (M := Option) e₀ W =
            Expr.denoteM (M := Option) (⟨op, rfl, args⟩ : Expr d _ _) V := hden₀
        have hlk : Expr.ctLeak MT e₀ W =
            Expr.ctLeak M (⟨op, rfl, args⟩ : Expr d _ _) V := hlk₀
        split at hr
        · rename_i c hc
          obtain ⟨rk, hk, rfl⟩ := Option.map_eq_some_iff.mp hr
          simp only [NFProg.leakRunM, hden, hlk]
          cases hx : Expr.denoteM (M := Option) (⟨op, rfl, args⟩ : Expr d _ _) V with
          | none => exact .none
          | some x =>
              simp only [Option.bind_some, hL.constE_denote, hL.constE_leak, Option.map_map]
              exact rel_map_ev (R := fun b b' => b = readMarks (L.rd j) rk.1 _ b') _
                (ih _ rk hk _ _ (hρ.cons2 x _ (hL.const j op c hc _ x hx)))
        · obtain ⟨rk, hk, rfl⟩ := Option.map_eq_some_iff.mp hr
          simp only [NFProg.leakRunM, hden, hlk]
          cases hx : Expr.denoteM (M := Option) (⟨op, rfl, args⟩ : Expr d _ _) V with
          | none => exact .none
          | some x =>
              simp only [Option.bind_some]
              exact rel_map_ev (R := fun b b' => b = readMarks (L.rd j) rk.1 _ b') _
                (ih _ rk hk _ _ (hρ.cons false x x rfl))
  | forLoop count inits body k ihb ihk =>
      intro Δ ρ a hr V W hρ
      simp only [liftAlong] at hr
      obtain ⟨c', hc, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨ri, hi, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨rb, hb, hr⟩ := Option.bind_eq_some_iff.mp hr
      split at hr
      · rename_i h
        obtain ⟨rk, hk, rfl⟩ := Option.map_eq_some_iff.mp hr
        obtain ⟨rmb, body'⟩ := rb
        obtain ⟨cm, inits'⟩ := ri
        dsimp only at h hb hk
        subst h
        have hcnt : c'.lookup W = count.lookup V := (hρ _ count).1 c' hc
        simp only [NFProg.leakRunM, castMask]
        rw [show HasWord64.toNat (d := tileSide d O) (c'.lookup W) =
          HasWord64.toNat (d := d) (count.lookup V) from
            congrArg (HasWord64.toNat (d := d)) hcnt]
        exact rel_bind_map (RA := fun b b' => b = readMarks (L.rd j) rmb _ b')
          (RB := fun b b' => b = readMarks (L.rd j) rk.1 _ b')
          (c := fun b => NFProg.leakRunM M fuel k (hvAppend b V))
          (c' := fun b' => NFProg.leakRunM MT fuel rk.2 (hvAppend b' W))
          (fun x y => .trip _ :: (x ++ y))
          (NFProg.forIterLeak_rel_bisim (R := fun b b' => b = readMarks (L.rd j) rmb _ b')
            (step := fun i acc => NFProg.leakRunM M fuel body
              (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
            (step' := fun i acc => NFProg.leakRunM MT fuel body'
              (hvAppend acc (.cons (HasWord64.ofNat (d := tileSide d O) i) W))) _
            (fun i _ b b' hbb => by
              subst hbb
              exact ihb _ ⟨rmb, body'⟩ hb _ _
                ((hρ.cons false (t := HasWord64.word (d := d)) (HasWord64.ofNat (d := d) i) _
                  rfl).app rmb _ b')) _ _
            (boundaryArgs_sound hρ inits ⟨rmb, inits'⟩ hi))
          (fun b b' hbb => by
            subst hbb
            exact ihk _ rk hk _ _ (hρ.app rmb _ b'))
      · cases hr
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ρ a hr V W hρ
      simp only [liftAlong] at hr
      obtain ⟨c', hc, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨rt, ht, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨re, he, hr⟩ := Option.bind_eq_some_iff.mp hr
      split at hr
      · rename_i h
        obtain ⟨rk, hk, rfl⟩ := Option.map_eq_some_iff.mp hr
        obtain ⟨rme, els'⟩ := re
        obtain ⟨rmt, thn'⟩ := rt
        dsimp only at h he hk
        subst h
        have hcnd : c'.lookup W = cond.lookup V := (hρ _ cond).1 c' hc
        simp only [NFProg.leakRunM, castMask]
        rw [show HasBoolBit.toBool (d := tileSide d O) (c'.lookup W) =
          HasBoolBit.toBool (d := d) (cond.lookup V) from
            congrArg (HasBoolBit.toBool (d := d)) hcnd]
        refine rel_bind_map (RA := fun b b' => b = readMarks (L.rd j) rme _ b')
          (RB := fun b b' => b = readMarks (L.rd j) rk.1 _ b')
          (c := fun b => NFProg.leakRunM M fuel k (hvAppend b V))
          (c' := fun b' => NFProg.leakRunM MT fuel rk.2 (hvAppend b' W))
          (fun x y => .branch _ :: (x ++ y)) ?_
          (fun b b' hbb => by
            subst hbb
            exact ihk _ rk hk _ _ (hρ.app rme _ b'))
        split
        · exact iht _ ⟨rme, thn'⟩ ht _ _ hρ
        · exact ihe _ ⟨rme, els'⟩ he _ _ hρ
      · cases hr
  | whileLoop inits body k ihb ihk =>
      intro Δ ρ a hr V W hρ
      simp only [liftAlong] at hr
      obtain ⟨ri, hi, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨rb, hb, hr⟩ := Option.bind_eq_some_iff.mp hr
      split at hr
      · rename_i h
        obtain ⟨rk, hk, rfl⟩ := Option.map_eq_some_iff.mp hr
        obtain ⟨rmb, body'⟩ := rb
        obtain ⟨cm, inits'⟩ := ri
        dsimp only at h hb hk
        subst h
        simp only [NFProg.leakRunM, castMask]
        exact rel_bind_map (RA := fun b b' => b = readMarks (L.rd j) cm _ b')
          (RB := fun b b' => b = readMarks (L.rd j) rk.1 _ b')
          (c := fun b => NFProg.leakRunM M fuel k (hvAppend b V))
          (c' := fun b' => NFProg.leakRunM MT fuel rk.2 (hvAppend b' W))
          (fun x y => x ++ y)
          (NFProg.whileIterLeak_rel_bisim (d := d) (d' := tileSide d O)
            (cs' := markTys n w cm _) (R := fun b b' => b = readMarks (L.rd j) cm _ b')
            (step := fun acc => NFProg.leakRunM M fuel body (hvAppend acc V))
            (step' := fun acc => NFProg.leakRunM MT fuel body' (hvAppend acc W))
            (fun b b' hbb => by
              subst hbb
              refine rel_mono ?_ (ihb _ ⟨false :: cm, body'⟩ hb _ _ (hρ.app cm _ b'))
              rintro u u' ⟨h1, h2⟩
              rw [readMarks_cons] at h1
              exact ⟨by rw [h1]; rfl, by rw [h1]; rfl, h2⟩) fuel _ _
            (boundaryArgs_sound hρ inits ⟨cm, inits'⟩ hi))
          (fun b b' hbb => by
            subst hbb
            exact ihk _ rk hk _ _ (hρ.app cm _ b'))
      · cases hr
  | call f args k ih =>
      intro Δ ρ a hr V W hρ
      cases hr

end LaneSound

variable {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} {ρ : Env n w Γ Δ}
  {V : Valuation Γ} {W : Valuation Δ} {j : Fin n}

theorem pick_sound (hρ : EnvRel j ρ V W) {t : JasminTy} (v : Var Γ t)
    {bv : (b : Bool) × Var Δ (liftTy n w b t)} (h : (ρ t v).pick = some bv) :
    outRd j bv.1 t (bv.2.lookup W) = v.lookup V :=
  LaneForms.pick_sound (d := jasminDialect) (O := Sum JasminOp TileOp) hρ v h

theorem retArgs_sound (hρ : EnvRel j ρ V W) {ts : List JasminTy}
    (vs : HVector (fun t => Var Γ t) ts)
    (r : (rm : List Bool) × HVector (fun t => Var Δ t) (liftTys n w rm ts))
    (h : retArgs n w ρ vs = some r) :
    Expr.lookupArgs vs V = laneOuts j r.1 ts (Expr.lookupArgs r.2 W) :=
  boundaryArgs_sound (d := jasminDialect) (O := Sum JasminOp TileOp) hρ vs r h

theorem scArgs_sound (hρ : EnvRel j ρ V W) {ts : List JasminTy}
    (vs : HVector (fun t => Var Γ t) ts)
    (as : HVector (fun t => Var Δ t) (ts.map (Sum.inl (β := TileTy))))
    (h : scArgs n w ρ vs = some as) :
    unmapInl (d := jasminDialect) (e := tileDialect) (Expr.lookupArgs as W) =
      Expr.lookupArgs vs V :=
  scalarArgs_sound (d := jasminDialect) (O := Sum JasminOp TileOp) hρ vs as h

theorem tileOp?_sound (M : LeakModel jasminDialect) (hρ : EnvRel j ρ V W) (op : JasminOp)
    (args : HVector (fun t => Var Γ t) (DialectSignature.sig op))
    (e' : Expr jasminTileDialect Δ (Sum.inr (TileTy.tile n w)))
    (h : tileOp? n w ρ op args = some e') :
    isLaneOp w op = true ∧ ∃ x' : Fin n → BitVec w,
      e'.denoteM (M := Option) W = some x' ∧
      laneRd j (DialectSignature.ret (d := jasminDialect) op) x' =
        DialectDenote.denote op (Expr.lookupArgs args V) ∧
      Expr.ctLeak (scalarTileLeak jasminDialect M) e' W = [] := by
  cases op <;> simp only [tileOp?] at h <;> try cases h
  case regArith bop w' =>
    split at h
    · rename_i hw
      subst hw
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      cases args with
      | cons x rest =>
        cases rest with
        | cons y rest2 =>
          cases rest2
          have h1 := (hρ _ x).2 a ha
          have h2 := (hρ _ y).2 b hb
          rw [laneRd_reg] at h1 h2
          refine ⟨by simp [isLaneOp], _, rfl, ?_, rfl⟩
          show laneRd j (.reg _) _ = bop.apply (x.lookup V) (y.lookup V)
          rw [laneRd_reg, ← h1, ← h2]
          rfl
    · cases h
  case mulhi w' =>
    split at h
    · rename_i hw
      subst hw
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      cases args with
      | cons x rest =>
        cases rest with
        | cons y rest2 =>
          cases rest2
          have h1 := (hρ _ x).2 a ha
          have h2 := (hρ _ y).2 b hb
          rw [laneRd_reg] at h1 h2
          refine ⟨by simp [isLaneOp], _, rfl, ?_, rfl⟩
          show laneRd j (.reg _) _ = mulHiW (x.lookup V) (y.lookup V)
          rw [laneRd_reg, ← h1, ← h2]
          rfl
    · cases h
  all_goals
    split at h
    · rename_i hw
      subst hw
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      cases args with
      | cons x rest =>
        cases rest
        have h1 := (hρ _ x).2 a ha
        rw [laneRd_reg] at h1
        refine ⟨by simp [isLaneOp], _, rfl, ?_, rfl⟩
        show laneRd j (.reg _) _ = _
        rw [laneRd_reg]
        have h3 : Expr.lookupArgs (d := jasminDialect) (HVector.cons x HVector.nil) V =
            HVector.cons (f := fun t : JasminTy => ⟦t⟧) (t := JasminTy.reg _)
              (a.lookup W j) HVector.nil := by
          rw [h1]
          rfl
        rw [h3]
        rfl
    · cases h

theorem constOf?_lane (j : Fin n) (op : JasminOp) (c : Nat) (h : constOf? w op = some c)
    (vals : HVector (fun t : JasminTy => ⟦t⟧) (DialectSignature.sig (d := jasminDialect) op)) :
    laneRd j (DialectSignature.ret (d := jasminDialect) op) (tileConstApply n w c) =
      DialectDenote.denote (d := jasminDialect) op vals := by
  cases op <;> simp only [constOf?] at h <;> try cases h
  split at h
  · rename_i hw
    subst hw
    cases h
    exact laneRd_reg j _
  · cases h

/-- **The laws of `jasminLane`** at a leakage model `M` of `jasminDialect` and its coproduct
    `scalarTileLeak jasminDialect M`. -/
theorem jasminLane_sound (M : LeakModel jasminDialect) :
    (jasminLane n w).Sound M (scalarTileLeak jasminDialect M) where
  tile := fun hρ op args e' h => by
    obtain ⟨hl, x', hx', hlane, hleak⟩ := tileOp?_sound M hρ op args e' h
    exact ⟨hl, x', hx', congrArg some hlane.symm, hleak⟩
  const := fun j op c h vals x hx => by
    cases hx
    exact constOf?_lane j op c h vals
  constE_denote := fun _ _ _ => rfl
  constE_leak := fun _ _ _ => rfl
  keep := fun op _ as e' W h => by
    cases h
    exact ⟨rfl, scalarTile_opLeak_inl jasminDialect M op _⟩

/-- The leakage models in which every scalar operation with a tile counterpart at lane
    width `w` is quiet. -/
def LaneQuiet (w : Nat) (M : LeakModel jasminDialect) : Prop :=
  ∀ op, isLaneOp w op = true → M.kind op = .quiet

/-- **The lifting preserves runs at every lane.** For a program `liftP` accepts along
    `ρ`, a leakage model in which the lifted scalar operations are quiet, and valuations
    related at lane `j`, the scalar run and the lifted run both fail, or both succeed
    with lane `j` of the lifted results equal to the scalar results and equal events. -/
theorem liftP_leakRun (M : LeakModel jasminDialect) (hM : LaneQuiet w M) (fuel : Nat)
    (j : Fin n) {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminTileDialect} (ρ : Env n w Γ Δ)
      (r : (rm : List Bool) × NFProg jasminTileDialect Δ (liftTys n w rm ts)),
      liftP n w p ρ = some r → ∀ (V : Valuation Γ) (W : Valuation Δ), EnvRel j ρ V W →
      Option.Rel (fun a a' => a.1 = laneOuts j r.1 ts a'.1 ∧ a.2 = a'.2)
        (NFProg.leakRunM M fuel p V)
        (NFProg.leakRunM (scalarTileLeak jasminDialect M) fuel r.2 W) :=
  fun ρ r hr V W hρ =>
    liftAlong_leakRun (jasminLane n w) M (scalarTileLeak jasminDialect M) (jasminLane_sound M)
      hM fuel j p ρ r hr V W hρ

end Sound

/-! ## 5. The lane theorems -/

section LaneTop

variable {n w : Nat} {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [HasWord64 d]
  [HasBoolBit d] {O : Type} [DialectSignature (tileSide d O)] [DialectDenoteM d Option]
  [DialectDenoteM (tileSide d O) Option]

/-- **Lane lifting at a table preserves runs at every lane.** For a program `q` that
    `tableLift L` returns on `p`, a lane `j` and a tile valuation `W`: the run of `p` on lane
    `j` of `W` and the run of `q` on `W` both fail, or both succeed with lane `j` of the
    results of `q` equal to the results of `p` and with equal events. -/
theorem tableLift_leakRun (L : LaneTable d O n w) (M : LeakModel d)
    (MT : LeakModel (tileSide d O)) (hL : L.Sound M MT)
    (hM : ∀ op, L.isLane op = true → M.kind op = .quiet) (fuel : Nat) (j : Fin n)
    (m rm : List Bool) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (q : NFProg (tileSide d O) (markTys n w m Γ) (markTys n w rm ts))
    (h : tableLift L m rm p = some q) (W : Valuation (d := tileSide d O) (markTys n w m Γ)) :
    Option.Rel (fun b b' => b.1 = readMarks (L.rd j) rm ts b'.1 ∧ b.2 = b'.2)
      (NFProg.leakRunM M fuel p (readMarks (L.rd j) m Γ W)) (NFProg.leakRunM MT fuel q W) := by
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hh
    obtain ⟨rm', q'⟩ := a
    dsimp only at hh
    subst hh
    cases h
    exact liftAlong_leakRun L M MT hL hM fuel j p _ _ ha _ _ (LaneRel.ofMask (L.rd j) m Γ W)
  · cases h

/-- **The events of a run lifted at a table** are the events of the scalar run on each
    lane. -/
theorem tableLift_events (L : LaneTable d O n w) (M : LeakModel d)
    (MT : LeakModel (tileSide d O)) (hL : L.Sound M MT)
    (hM : ∀ op, L.isLane op = true → M.kind op = .quiet) (fuel : Nat) (j : Fin n)
    (m rm : List Bool) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (q : NFProg (tileSide d O) (markTys n w m Γ) (markTys n w rm ts))
    (h : tableLift L m rm p = some q) (W : Valuation (d := tileSide d O) (markTys n w m Γ)) :
    (NFProg.leakRunM MT fuel q W).map Prod.snd =
      (NFProg.leakRunM M fuel p (readMarks (L.rd j) m Γ W)).map Prod.snd :=
  rel_snd (R := fun b b' => b = readMarks (L.rd j) rm ts b')
    (tableLift_leakRun L M MT hL hM fuel j m rm p q h W)

/-- **The lane theorem at a table.** Lane `j` of the denotation of a lifted program on a
    tile valuation `W` is the denotation of the scalar program on lane `j` of `W`, at every
    fuel, in the empty call environment. -/
theorem tableLift_denote (L : LaneTable d O n w) (M : LeakModel d)
    (MT : LeakModel (tileSide d O)) (hL : L.Sound M MT)
    (hM : ∀ op, L.isLane op = true → M.kind op = .quiet) (fuel : Nat) (j : Fin n)
    (m rm : List Bool) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (q : NFProg (tileSide d O) (markTys n w m Γ) (markTys n w rm ts))
    (h : tableLift L m rm p = some q) (W : Valuation (d := tileSide d O) (markTys n w m Γ)) :
    (q.denoteAt CallEnv.empty fuel W).map (readMarks (L.rd j) rm ts) =
      p.denoteAt CallEnv.empty fuel (readMarks (L.rd j) m Γ W) := by
  rw [← NFProg.leakRunM_fst M fuel p, ← NFProg.leakRunM_fst MT fuel q]
  exact rel_fst (tableLift_leakRun L M MT hL hM fuel j m rm p q h W)

/-- The semantics of programs of a dialect at the fuel `fuel` in the empty call
    environment. -/
def denoteSem (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d] [HasWord64 d]
    [HasBoolBit d] [DialectDenoteM d Option] (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    PassChain.Sem (NFProg d Γ ts) where
  In := Valuation Γ
  Out := Valuation ts
  den := fun p V => p.denoteAt CallEnv.empty fuel V

/-- The leak semantics of programs of a dialect at the model `M`: the events of
    `NFProg.leakRunM`. -/
def eventSem {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [HasWord64 d]
    [HasBoolBit d] [DialectDenoteM d Option] (M : LeakModel d) (fuel : Nat) (Γ : Ctxt d)
    (ts : List d.Ty) : PassChain.LeakSem (NFProg d Γ ts) where
  In := Valuation Γ
  Ev := CTLeak
  leak p V := (NFProg.leakRunM M fuel p V).map Prod.snd

open PassChain in
/-- **The certificate of lane lifting at a table, at lane `j`.** The step `tableLift L m rm`
    between the semantics `denoteSem` of the two dialects: the input relation holds of a
    scalar valuation and a tile valuation when the first is lane `j` of the second, and the
    output relation likewise of the result tuples. -/
def tableLiftCert (L : LaneTable d O n w) (M : LeakModel d) (MT : LeakModel (tileSide d O))
    (hL : L.Sound M MT) (hM : ∀ op, L.isLane op = true → M.kind op = .quiet) (j : Fin n)
    (m rm : List Bool) (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    StepCert (tableLift L m rm (Γ := Γ) (ts := ts)) (denoteSem d fuel Γ ts)
      (denoteSem (tileSide d O) fuel (markTys n w m Γ) (markTys n w rm ts)) where
  relIn V W := V = readMarks (L.rd j) m Γ W
  relOut o o' := o = readMarks (L.rd j) rm ts o'
  sound := by
    intro p q V W o hf hVW hd
    subst hVW
    have h1 := tableLift_denote L M MT hL hM fuel j m rm p q hf W
    rw [show p.denoteAt CallEnv.empty fuel (readMarks (L.rd j) m Γ W) = some o from hd] at h1
    obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.mp h1
    exact ⟨o', ho', rfl⟩

open PassChain in
/-- **The leakage certificate of lane lifting at a table, at lane `j`.** Between the
    two-run semantics of the two leak semantics: the input relation holds when each scalar
    valuation is lane `j` of the tile valuation, and the output relation is the equality of
    the pairs of event lists. -/
def tableLiftLeakCert (L : LaneTable d O n w) (M : LeakModel d)
    (MT : LeakModel (tileSide d O)) (hL : L.Sound M MT)
    (hM : ∀ op, L.isLane op = true → M.kind op = .quiet) (j : Fin n) (m rm : List Bool)
    (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    StepCert (tableLift L m rm (Γ := Γ) (ts := ts)) (eventSem M fuel Γ ts).twoRun
      (eventSem MT fuel (markTys n w m Γ) (markTys n w rm ts)).twoRun where
  relIn V W := V.1 = readMarks (L.rd j) m Γ W.1 ∧ V.2 = readMarks (L.rd j) m Γ W.2
  relOut a b := b = a
  sound := by
    intro p q V W o hf hVW hd
    obtain ⟨V1, V2⟩ := V
    obtain ⟨h1, h2⟩ := hVW
    dsimp only at h1 h2
    subst h1 h2
    refine ⟨o, ?_, rfl⟩
    have e1 := tableLift_events L M MT hL hM fuel j m rm p q hf W.1
    have e2 := tableLift_events L M MT hL hM fuel j m rm p q hf W.2
    simp only [LeakSem.twoRun, eventSem] at hd ⊢
    rw [e1, e2]
    exact hd

/-- The output relation of `tableLiftLeakCert` implies the constant-time relation. -/
theorem tableLiftLeakCert_ct (L : LaneTable d O n w) (M : LeakModel d)
    (MT : LeakModel (tileSide d O)) (hL : L.Sound M MT)
    (hM : ∀ op, L.isLane op = true → M.kind op = .quiet) (j : Fin n) (m rm : List Bool)
    (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    ∀ a b, (tableLiftLeakCert L M MT hL hM j m rm fuel Γ ts).relOut a b →
      PassChain.ctRel a b := by
  intro a b h hab
  cases h
  exact hab

end LaneTop

section Top

variable {n w : Nat}

/-- **Lane lifting preserves runs at every lane.** For a lifted program `q` of `p`, a
    leakage model in which the lifted scalar operations are quiet, a lane `j` and a tile
    valuation `W`: the run of `p` on lane `j` of `W` and the run of `q` on `W` both fail,
    or both succeed with lane `j` of the results of `q` equal to the results of `p` and
    with equal events. -/
theorem laneLift_leakRun (M : LeakModel jasminDialect) (hM : LaneQuiet w M) (fuel : Nat)
    (j : Fin n) (m rm : List Bool) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts)
    (q : NFProg jasminTileDialect (liftTys n w m Γ) (liftTys n w rm ts))
    (h : laneLift n w m rm p = some q)
    (W : Valuation (d := jasminTileDialect) (liftTys n w m Γ)) :
    Option.Rel (fun a a' => a.1 = laneOuts j rm ts a'.1 ∧ a.2 = a'.2)
      (NFProg.leakRunM M fuel p (laneOuts j m Γ W))
      (scalarTileLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel
        q W) :=
  tableLift_leakRun (jasminLane n w) M (scalarTileLeak jasminDialect M) (jasminLane_sound M)
    hM fuel j m rm p q h W

/-- **The events of a lifted run** are the events of the scalar run on each lane. -/
theorem laneLift_events (M : LeakModel jasminDialect) (hM : LaneQuiet w M) (fuel : Nat)
    (j : Fin n) (m rm : List Bool) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts)
    (q : NFProg jasminTileDialect (liftTys n w m Γ) (liftTys n w rm ts))
    (h : laneLift n w m rm p = some q)
    (W : Valuation (d := jasminTileDialect) (liftTys n w m Γ)) :
    (scalarTileLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M fuel
        q W).map Prod.snd =
      (NFProg.leakRunM M fuel p (laneOuts j m Γ W)).map Prod.snd :=
  rel_snd (R := fun a a' => a = laneOuts j rm ts a') (laneLift_leakRun M hM fuel j m rm p q h W)

/-- The leakage model of `jasminDialect` in which every operation is quiet. -/
def quietModel : LeakModel jasminDialect := ⟨fun _ => .quiet, fun _ _ => 0⟩

/-- **The lane theorem.** Lane `j` of the denotation of a lifted program on a tile
    valuation `W` is the denotation of the scalar program on lane `j` of `W`, at every
    fuel. -/
theorem laneLift_denote (fuel : Nat) (j : Fin n) (m rm : List Bool)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (q : NFProg jasminTileDialect (liftTys n w m Γ) (liftTys n w rm ts))
    (h : laneLift n w m rm p = some q)
    (W : Valuation (d := jasminTileDialect) (liftTys n w m Γ)) :
    (scalarTileDenP jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) fuel q
        W).map (laneOuts j rm ts) =
      p.denote fuel (laneOuts j m Γ W) :=
  tableLift_denote (jasminLane n w) quietModel (scalarTileLeak jasminDialect quietModel)
    (jasminLane_sound quietModel) (fun _ _ => rfl) fuel j m rm p q h W

/-- The semantics of scalar programs at the fuel `fuel`: `NFProg.denote fuel`. -/
def scalarSem (fuel : Nat) (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    PassChain.Sem (NFProg jasminDialect Γ ts) where
  In := Valuation (d := jasminDialect) Γ
  Out := Valuation (d := jasminDialect) ts
  den := fun (p : NFProg jasminDialect Γ ts) (V : Valuation (d := jasminDialect) Γ) =>
    p.denote fuel V

/-- The semantics of programs of `jasminTileDialect` at the fuel `fuel`. -/
def tileSem (fuel : Nat) (Δ : Ctxt jasminTileDialect) (ts : List jasminTileDialect.Ty) :
    PassChain.Sem (NFProg jasminTileDialect Δ ts) where
  In := Valuation (d := jasminTileDialect) Δ
  Out := Valuation (d := jasminTileDialect) ts
  den := fun (q : NFProg jasminTileDialect Δ ts) (W : Valuation (d := jasminTileDialect) Δ) =>
    scalarTileDenP jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) fuel q W

open PassChain in
/-- **The certificate of lane lifting at lane `j`.** The step `laneLift n w m rm` from the
    semantics `NFProg.denote fuel` of scalar programs to that of programs of
    `jasminTileDialect`: the input relation holds of a scalar valuation and a tile
    valuation when the first is lane `j` of the second, and the output relation likewise
    of the result tuples. -/
def laneLiftCert (j : Fin n) (m rm : List Bool) (fuel : Nat) (Γ : Ctxt jasminDialect)
    (ts : List JasminTy) :
    StepCert (laneLift n w m rm (Γ := Γ) (ts := ts))
      (scalarSem fuel Γ ts) (tileSem fuel (liftTys n w m Γ) (liftTys n w rm ts)) :=
  tableLiftCert (jasminLane n w) quietModel (scalarTileLeak jasminDialect quietModel)
    (jasminLane_sound quietModel) (fun _ _ => rfl) j m rm fuel Γ ts

/-- The leak semantics of scalar programs at the model `M`: the events of
    `NFProg.leakRunM`. -/
def scalarLeakSem (M : LeakModel jasminDialect) (fuel : Nat) (Γ : Ctxt jasminDialect)
    (ts : List JasminTy) : PassChain.LeakSem (NFProg jasminDialect Γ ts) where
  In := Valuation Γ
  Ev := CTLeak
  leak p V := (NFProg.leakRunM M fuel p V).map Prod.snd

/-- The leak semantics of programs of `jasminTileDialect` at the model
    `scalarTileLeak jasminDialect M`. -/
def tileLeakSem (M : LeakModel jasminDialect) (fuel : Nat) (Δ : Ctxt jasminTileDialect)
    (ts : List jasminTileDialect.Ty) : PassChain.LeakSem (NFProg jasminTileDialect Δ ts) where
  In := Valuation Δ
  Ev := CTLeak
  leak q W := (scalarTileLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect)
    M fuel q W).map Prod.snd

open PassChain in
/-- **The leakage certificate of lane lifting at lane `j`.** Between the two-run
    semantics of the two leak semantics: the input relation holds when each scalar
    valuation is lane `j` of the tile valuation, and the output relation is the equality
    of the pairs of event lists. -/
def laneLiftLeakCert (M : LeakModel jasminDialect) (hM : LaneQuiet w M) (j : Fin n)
    (m rm : List Bool) (fuel : Nat) (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    StepCert (laneLift n w m rm (Γ := Γ) (ts := ts))
      (scalarLeakSem M fuel Γ ts).twoRun
      (tileLeakSem M fuel (liftTys n w m Γ) (liftTys n w rm ts)).twoRun :=
  tableLiftLeakCert (jasminLane n w) M (scalarTileLeak jasminDialect M) (jasminLane_sound M)
    hM j m rm fuel Γ ts

/-- The output relation of `laneLiftLeakCert` implies the constant-time relation. -/
theorem laneLiftLeakCert_ct (M : LeakModel jasminDialect) (hM : LaneQuiet w M) (j : Fin n)
    (m rm : List Bool) (fuel : Nat) (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    ∀ a b, (laneLiftLeakCert M hM j m rm fuel Γ ts).relOut a b → PassChain.ctRel a b := by
  intro a b h hab
  cases h
  exact hab

end Top

/-! ## 6. The counted loop with a carried accumulator -/

section Instance

/-- The scalar counted loop that adds `x` to a carried word once per trip. The context is
    `[count, x, a]`: the trip count at `reg 64`, and two words of `w` bits. -/
def accLoop (w : Nat) : NFProg jasminDialect [.reg 64, .reg w, .reg w] [.reg w] :=
  NFProg.forLoop (d := jasminDialect) (cs := [.reg w]) (Γ := [.reg 64, .reg w, .reg w])
    .here (.cons (.there (.there .here)) .nil)
    (.var ⟨.regArith .add w, rfl,
        .cons .here (.cons (.there (.there (.there .here))) .nil)⟩
      (.ret (.cons .here .nil)))
    (.ret (.cons .here .nil))

/-- The lifting of `accLoop w` with the trip count scalar and the two words in lanes is
    `tileAccLoop`, at every lane count and width. -/
theorem laneLift_accLoop (n w : Nat) :
    laneLift n w [false, true, true] [true] (accLoop w) =
      some (tileAccLoop jasminDialect n w) := by
  simp [laneLift, tableLift, liftAlong, accLoop, jasminLane, tileOp?, LaneEnv.ofMask,
    LaneEnv.app, LaneEnv.cons, LaneForms.ofTag, LaneForms.wk, castMask]
  rfl

/-- **The lane theorem at `accLoop`.** Lane `j` of the result of `tileAccLoop` on the
    tiles `x` and `a` is the result of `accLoop` on the lanes `x j` and `a j`. -/
theorem accLoop_lane (n w : Nat) (fuel : Nat) (j : Fin n) (cnt : BitVec 64)
    (x a : Fin n → BitVec w) :
    (scalarTileDenP jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) fuel
        (tileAccLoop jasminDialect n w) (.cons cnt (.cons x (.cons a .nil)))).map
        (laneOuts j [true] [.reg w]) =
      (accLoop w).denote fuel (.cons cnt (.cons (x j) (.cons (a j) .nil))) := by
  have h := laneLift_denote fuel j [false, true, true] [true] (accLoop w) _
    (laneLift_accLoop n w) (.cons cnt (.cons x (.cons a .nil)))
  have hW : laneOuts j [false, true, true] [.reg 64, .reg w, .reg w]
      (.cons cnt (.cons x (.cons a .nil))) =
      .cons cnt (.cons (x j) (.cons (a j) .nil)) := by
    show HVector.cons _ (HVector.cons (laneRd j (.reg w) x)
      (HVector.cons (laneRd j (.reg w) a) .nil)) = _
    rw [laneRd_reg, laneRd_reg]
    rfl
  rw [hW] at h
  exact h

/-- The denotation of `accLoop` on lane `j` of the tiles `x` and `a`, from the lane
    theorem and `tileAccLoop_denote`. -/
theorem accLoop_denote_lane (n w : Nat) (fuel : Nat) (j : Fin n) (cnt : BitVec 64)
    (x a : Fin n → BitVec w) :
    (accLoop w).denote fuel (.cons cnt (.cons (x j) (.cons (a j) .nil))) =
      some (.cons (a j + BitVec.ofNat w cnt.toNat * x j) .nil) := by
  rw [← accLoop_lane n w fuel j cnt x a, tileAccLoop_denote]
  refine congrArg some ?_
  exact congrArg₂ HVector.cons
    (laneRd_reg (w := w) j (fun i => a i + BitVec.ofNat w cnt.toNat * x i)) rfl

/-- `accLoop` at 8 lanes of 64 bits. -/
theorem accLoop_lane_8x64 (fuel : Nat) (j : Fin 8) (cnt : BitVec 64)
    (x a : Fin 8 → BitVec 64) :
    (accLoop 64).denote fuel (.cons cnt (.cons (x j) (.cons (a j) .nil))) =
      some (.cons (a j + BitVec.ofNat 64 cnt.toNat * x j) .nil) :=
  accLoop_denote_lane 8 64 fuel j cnt x a

/-- `accLoop` at 16 lanes of 32 bits. -/
theorem accLoop_lane_16x32 (fuel : Nat) (j : Fin 16) (cnt : BitVec 64)
    (x a : Fin 16 → BitVec 32) :
    (accLoop 32).denote fuel (.cons cnt (.cons (x j) (.cons (a j) .nil))) =
      some (.cons (a j + BitVec.ofNat 32 cnt.toNat * x j) .nil) :=
  accLoop_denote_lane 16 32 fuel j cnt x a

end Instance

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapNF
