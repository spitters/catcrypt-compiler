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

## Main definitions

* `liftTy`, `liftTys` — the type map along a mask.
* `laneRd`, `outRd`, `laneOuts` — lane `k` of a tile, of a value and of a tuple.
* `LVar`, `Env`, `EnvRel` — the forms of a source variable in a target context, and the
  relation of a source valuation to a target valuation at lane `k`.
* `liftP`, `laneLift` — the lifting along an environment, and at entry and result masks.
* `LaneQuiet` — the leakage models in which the lifted scalar operations are quiet.
* `laneLiftCert`, `laneLiftLeakCert` — the step certificates at lane `k`.
* `accLoop` — the scalar counted loop with a carried accumulator.

## Main results

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

section Types

variable (n w : Nat)

/-- The type of a variable of type `t` in the lifted program: the tile of `n` lanes of
    `w` bits when the variable is marked as lane data, the scalar type `t` otherwise. -/
def liftTy (b : Bool) (t : JasminTy) : jasminTileDialect.Ty :=
  match b with
  | true => .inr (.tile n w)
  | false => .inl t

/-- The lifted type list along a mask; a position past the end of the mask is scalar. -/
def liftTys : List Bool → List JasminTy → List jasminTileDialect.Ty
  | _, [] => []
  | rm, t :: ts => liftTy n w (rm.headD false) t :: liftTys rm.tail ts

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
  match b with
  | true => fun x => laneRd k t x
  | false => fun x => x

/-- Lane `k` of a lifted tuple. -/
def laneOuts (k : Fin n) : (rm : List Bool) → (ts : List JasminTy) →
    Valuation (d := jasminTileDialect) (liftTys n w rm ts) → Valuation (d := jasminDialect) ts
  | _, [], _ => .nil
  | rm, t :: ts, .cons x xs => .cons (outRd k (rm.headD false) t x) (laneOuts k rm.tail ts xs)

/-- Lane `k` of a non-empty lifted tuple, by head and tail. -/
theorem laneOuts_cons (k : Fin n) (rm : List Bool) (t : JasminTy) (ts : List JasminTy)
    (o : Valuation (d := jasminTileDialect) (liftTys n w rm (t :: ts))) :
    laneOuts k rm (t :: ts) o =
      .cons (outRd k (rm.headD false) t o.head) (laneOuts k rm.tail ts o.tail) := by
  cases o
  rfl

end Types

/-! ## 2. Environments -/

section Envs

variable (n w : Nat)

/-- The forms of a source variable of type `t` in the target context `Δ`: a scalar
    variable, a tile variable, or both. -/
structure LVar (Δ : Ctxt jasminTileDialect) (t : JasminTy) where
  /-- The scalar form. -/
  sc : Option (Var Δ (Sum.inl t))
  /-- The tile form. -/
  ln : Option (Var Δ (Sum.inr (TileTy.tile n w)))

/-- An environment: the forms of every variable of `Γ` in `Δ`. -/
abbrev Env (Γ : Ctxt jasminDialect) (Δ : Ctxt jasminTileDialect) : Type :=
  ∀ t : JasminTy, Var Γ t → LVar n w Δ t

variable {n w}

/-- The forms of a variable under one more binding of the target context. -/
def LVar.wk {Δ : Ctxt jasminTileDialect} {t : JasminTy} (u : jasminTileDialect.Ty)
    (x : LVar n w Δ t) : LVar n w (u :: Δ) t :=
  ⟨x.sc.map .there, x.ln.map .there⟩

/-- The single form of a variable of the lifted type `liftTy n w b t`. -/
def LVar.ofTag {Δ : Ctxt jasminTileDialect} {t : JasminTy} (b : Bool) :
    Var Δ (liftTy n w b t) → LVar n w Δ t :=
  match b with
  | true => fun v => ⟨none, some v⟩
  | false => fun v => ⟨some v, none⟩

/-- The form of a variable at a region boundary: the scalar form when it exists, the tile
    form otherwise. -/
def LVar.pick {Δ : Ctxt jasminTileDialect} {t : JasminTy} (x : LVar n w Δ t) :
    Option ((b : Bool) × Var Δ (liftTy n w b t)) :=
  match x.sc, x.ln with
  | some v, _ => some ⟨false, v⟩
  | none, some v => some ⟨true, v⟩
  | none, none => none

/-- The environment under a binding of the form `b`. -/
def Env.cons {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} (ρ : Env n w Γ Δ)
    (b : Bool) {t : JasminTy} : Env n w (t :: Γ) (liftTy n w b t :: Δ)
  | _, .here => LVar.ofTag b .here
  | _, .there v => (ρ _ v).wk _

/-- The environment under a binding with both forms: the tile variable is bound last. -/
def Env.cons2 {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} (ρ : Env n w Γ Δ)
    {t : JasminTy} : Env n w (t :: Γ) (Sum.inr (TileTy.tile n w) :: Sum.inl t :: Δ)
  | _, .here => ⟨some (.there .here), some .here⟩
  | _, .there v => ((ρ _ v).wk _).wk _

/-- The environment under a tuple of bindings of the forms `rm`. -/
def Env.app {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} (ρ : Env n w Γ Δ) :
    (rm : List Bool) → (cs : List JasminTy) → Env n w (cs ++ Γ) (liftTys n w rm cs ++ Δ)
  | _, [] => ρ
  | rm, _ :: cs => (Env.app ρ rm.tail cs).cons (rm.headD false)

/-- The environment of the lifted context along the mask `m`. -/
def Env.ofMask : (m : List Bool) → (Γ : Ctxt jasminDialect) → Env n w Γ (liftTys n w m Γ)
  | _, [] => fun _ v => nomatch v
  | m, _ :: Γ => (Env.ofMask m.tail Γ).cons (m.headD false)

/-- A source valuation `V` is lane `k` of the target valuation `W` along `ρ`: a scalar
    form reads the source value, and lane `k` of a tile form is the source value. -/
def EnvRel (k : Fin n) {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect}
    (ρ : Env n w Γ Δ) (V : Valuation Γ) (W : Valuation Δ) : Prop :=
  ∀ (t : JasminTy) (v : Var Γ t),
    (∀ v', (ρ t v).sc = some v' → v'.lookup W = v.lookup V) ∧
    (∀ v', (ρ t v).ln = some v' → laneRd k t (v'.lookup W) = v.lookup V)

theorem EnvRel.cons {k : Fin n} {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect}
    {ρ : Env n w Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (hρ : EnvRel k ρ V W) (b : Bool)
    {t : JasminTy} (x' : ⟦liftTy n w b t⟧) (x : ⟦t⟧) (hx : outRd k b t x' = x) :
    EnvRel k (ρ.cons b (t := t)) (V.extend x) (W.extend x') := by
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

theorem EnvRel.cons2 {k : Fin n} {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect}
    {ρ : Env n w Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (hρ : EnvRel k ρ V W)
    {t : JasminTy} (x : ⟦t⟧) (xt : Fin n → BitVec w) (hx : laneRd k t xt = x) :
    EnvRel k (ρ.cons2 (t := t)) (V.extend x)
      (Valuation.extend (d := jasminTileDialect) (t := Sum.inr (TileTy.tile n w))
        (Valuation.extend (d := jasminTileDialect) (t := Sum.inl t) W x) xt) := by
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

theorem EnvRel.app {k : Fin n} {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect}
    {ρ : Env n w Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (hρ : EnvRel k ρ V W) :
    (rm : List Bool) → (cs : List JasminTy) →
    (a : Valuation (d := jasminTileDialect) (liftTys n w rm cs)) →
    EnvRel k (ρ.app rm cs) (hvAppend (laneOuts k rm cs a) V) (hvAppend a W)
  | _, [], .nil => hρ
  | rm, _ :: cs, .cons x xs =>
      EnvRel.cons (EnvRel.app hρ rm.tail cs xs) (rm.headD false) x _ rfl

theorem EnvRel.ofMask (k : Fin n) : (m : List Bool) → (Γ : Ctxt jasminDialect) →
    (W : Valuation (d := jasminTileDialect) (liftTys n w m Γ)) →
    EnvRel k (Env.ofMask m Γ) (laneOuts k m Γ W) W
  | _, [], _ => fun _ v => nomatch v
  | m, _ :: Γ, .cons x xs => EnvRel.cons (EnvRel.ofMask k m.tail Γ xs) (m.headD false) x _ rfl

end Envs

/-! ## 3. The lifting -/

section Lift

variable (n w : Nat)

/-- The variables of a region boundary in the forms `LVar.pick` chooses, with the mask of
    those forms. -/
def retArgs {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} (ρ : Env n w Γ Δ) :
    {ts : List JasminTy} → HVector (fun t => Var Γ t) ts →
    Option ((rm : List Bool) × HVector (fun t => Var Δ t) (liftTys n w rm ts))
  | [], .nil => some ⟨[], .nil⟩
  | _ :: _, .cons v vs =>
      (ρ _ v).pick.bind fun bv => (retArgs ρ vs).map fun r => ⟨bv.1 :: r.1, .cons bv.2 r.2⟩

/-- The scalar forms of an argument vector, when every argument has one. -/
def scArgs {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} (ρ : Env n w Γ Δ) :
    {ts : List JasminTy} → HVector (fun t => Var Γ t) ts →
    Option (HVector (fun t => Var Δ t) (ts.map (Sum.inl (β := TileTy))))
  | [], .nil => some .nil
  | _ :: _, .cons v vs => (ρ _ v).sc.bind fun v' => (scArgs ρ vs).map (.cons v')

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
  h ▸ q

/-- **The lifting along an environment.** The result is the mask of the forms of the
    returned variables and the lifted program; `none` where the program is refused. -/
def liftP : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts →
    {Δ : Ctxt jasminTileDialect} → Env n w Γ Δ →
    Option ((rm : List Bool) × NFProg jasminTileDialect Δ (liftTys n w rm ts))
  | _, _, .ret vs, _, ρ => (retArgs n w ρ vs).map fun r => ⟨r.1, .ret r.2⟩
  | _, _, .var e k, _, ρ =>
      match tileOp? n w ρ e.op e.args with
      | some e' => (liftP k (ρ.cons true)).map fun r => ⟨r.1, .var e' r.2⟩
      | none =>
          (scArgs n w ρ e.args).bind fun as =>
            match constOf? w e.op with
            | some c =>
                (liftP k ρ.cons2).map fun r =>
                  ⟨r.1, .var ⟨.inl e.op, congrArg Sum.inl e.retTy_eq, as⟩
                    (.var ⟨.inr (.tileConst n w c), rfl, .nil⟩ r.2)⟩
            | none =>
                (liftP k (ρ.cons false)).map fun r =>
                  ⟨r.1, .var ⟨.inl e.op, congrArg Sum.inl e.retTy_eq, as⟩ r.2⟩
  | _, _, .forLoop (cs := cs) count inits body k, _, ρ =>
      (ρ _ count).sc.bind fun c' =>
        (retArgs n w ρ inits).bind fun ri =>
          (liftP body (Env.app (ρ.cons false) ri.1 cs)).bind fun rb =>
            if h : rb.1 = ri.1 then
              (liftP k (Env.app ρ ri.1 cs)).map fun rk =>
                ⟨rk.1, .forLoop c' ri.2 (castRes n w h rb.2) rk.2⟩
            else none
  | _, _, .ifThenElse (rs := rs) cond thn els k, _, ρ =>
      (ρ _ cond).sc.bind fun c' =>
        (liftP thn ρ).bind fun rt =>
          (liftP els ρ).bind fun re =>
            if h : re.1 = rt.1 then
              (liftP k (Env.app ρ rt.1 rs)).map fun rk =>
                ⟨rk.1, .ifThenElse c' rt.2 (castRes n w h re.2) rk.2⟩
            else none
  | _, _, .whileLoop (cs := cs) inits body k, _, ρ =>
      (retArgs n w ρ inits).bind fun ri =>
        (liftP body (Env.app ρ ri.1 cs)).bind fun rb =>
          if h : rb.1 = false :: ri.1 then
            (liftP k (Env.app ρ ri.1 cs)).map fun rk =>
              ⟨rk.1, .whileLoop ri.2 (castRes n w h rb.2) rk.2⟩
          else none
  | _, _, .call .., _, _ => none

/-- **Lane lifting.** The lifting of `p` at the entry mask `m`, when the forms of its
    results are those of the mask `rm`. -/
def laneLift (m rm : List Bool) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    Option (NFProg jasminTileDialect (liftTys n w m Γ) (liftTys n w rm ts)) :=
  (liftP n w p (Env.ofMask m Γ)).bind fun r => if h : r.1 = rm then some (castRes n w h r.2) else none

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

variable {Γ : Ctxt jasminDialect} {Δ : Ctxt jasminTileDialect} {ρ : Env n w Γ Δ}
  {V : Valuation Γ} {W : Valuation Δ} {j : Fin n}

theorem pick_sound (hρ : EnvRel j ρ V W) {t : JasminTy} (v : Var Γ t)
    {bv : (b : Bool) × Var Δ (liftTy n w b t)} (h : (ρ t v).pick = some bv) :
    outRd j bv.1 t (bv.2.lookup W) = v.lookup V := by
  unfold LVar.pick at h
  split at h
  · cases h
    exact (hρ t v).1 _ ‹_›
  · cases h
    exact (hρ t v).2 _ ‹_›
  · cases h

theorem retArgs_sound (hρ : EnvRel j ρ V W) : {ts : List JasminTy} →
    (vs : HVector (fun t => Var Γ t) ts) →
    (r : (rm : List Bool) × HVector (fun t => Var Δ t) (liftTys n w rm ts)) →
    retArgs n w ρ vs = some r →
    Expr.lookupArgs vs V = laneOuts j r.1 ts (Expr.lookupArgs r.2 W)
  | [], .nil, r, h => by cases h; rfl
  | _ :: _, .cons v vs, r, h => by
      obtain ⟨bv, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp h
      exact congrArg₂ HVector.cons (pick_sound hρ v hb).symm (retArgs_sound hρ vs r' hr)

theorem scArgs_sound (hρ : EnvRel j ρ V W) : {ts : List JasminTy} →
    (vs : HVector (fun t => Var Γ t) ts) →
    (as : HVector (fun t => Var Δ t) (ts.map (Sum.inl (β := TileTy)))) →
    scArgs n w ρ vs = some as →
    unmapInl (d := jasminDialect) (e := tileDialect) (Expr.lookupArgs as W) =
      Expr.lookupArgs vs V
  | [], .nil, _, _ => rfl
  | _ :: _, .cons v vs, as, h => by
      obtain ⟨v', hv, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨as', ha, rfl⟩ := Option.map_eq_some_iff.mp h
      exact congrArg₂ HVector.cons ((hρ _ v).1 v' hv) (scArgs_sound hρ vs as' ha)

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
        (NFProg.leakRunM (scalarTileLeak jasminDialect M) fuel r.2 W) := by
  induction p with
  | ret vs =>
      intro Δ ρ r hr V W hρ
      obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp hr
      exact .some ⟨retArgs_sound hρ vs r' h', rfl⟩
  | var e k ih =>
      intro Δ ρ r hr V W hρ
      obtain ⟨op, rfl, args⟩ := e
      simp only [liftP] at hr
      split at hr
      · rename_i e' he
        obtain ⟨rk, hk, rfl⟩ := Option.map_eq_some_iff.mp hr
        obtain ⟨hl, x', hx', hlane, hleak⟩ := tileOp?_sound M hρ op args e' he
        have hsrc : Expr.ctLeak M (⟨op, rfl, args⟩ : Expr jasminDialect _ _) V = [] := by
          unfold Expr.ctLeak opLeak
          rw [hM _ hl]
        simp only [NFProg.leakRunM, Expr.denoteM_option_eq_some, Option.bind_some, hx', hleak,
          hsrc]
        exact rel_map_ev (R := fun a a' => a = laneOuts j rk.1 _ a') _
          (ih _ rk hk _ _ (hρ.cons true x' _ hlane))
      · obtain ⟨as, has, hr⟩ := Option.bind_eq_some_iff.mp hr
        have hargs := scArgs_sound hρ args as has
        have hden : Expr.denoteM (M := Option)
            (⟨.inl op, rfl, as⟩ : Expr jasminTileDialect Δ
              (Sum.inl (DialectSignature.ret (d := jasminDialect) op))) W =
            some (DialectDenote.denote op (Expr.lookupArgs args V)) := by
          rw [← hargs]
          rfl
        have hlk : Expr.ctLeak (scalarTileLeak jasminDialect M)
            (⟨.inl op, rfl, as⟩ : Expr jasminTileDialect Δ
              (Sum.inl (DialectSignature.ret (d := jasminDialect) op))) W =
            Expr.ctLeak M (⟨op, rfl, args⟩ : Expr jasminDialect _ _) V := by
          show opLeak (scalarTileLeak jasminDialect M) (Sum.inl op) _ = opLeak M op _
          rw [scalarTile_opLeak_inl, hargs]
        split at hr
        · rename_i c hc
          obtain ⟨rk, hk, rfl⟩ := Option.map_eq_some_iff.mp hr
          have hct : ∀ {Δ' : Ctxt jasminTileDialect} (W' : Valuation Δ'),
              Expr.denoteM (M := Option) (⟨.inr (.tileConst n w c), rfl, .nil⟩ :
                Expr jasminTileDialect Δ' (Sum.inr (TileTy.tile n w))) W' =
              some (tileConstApply n w c) := fun _ => rfl
          have hcl : ∀ {Δ' : Ctxt jasminTileDialect} (W' : Valuation Δ'),
              Expr.ctLeak (scalarTileLeak jasminDialect M) (⟨.inr (.tileConst n w c), rfl, .nil⟩ :
                Expr jasminTileDialect Δ' (Sum.inr (TileTy.tile n w))) W' = [] := fun _ => rfl
          simp only [NFProg.leakRunM, Expr.denoteM_option_eq_some, Option.bind_some, hden, hlk,
            hct, hcl, Option.map_map]
          exact rel_map_ev (R := fun a a' => a = laneOuts j rk.1 _ a') _
            (ih _ rk hk _ _ (hρ.cons2 _ _ (constOf?_lane j op c hc _)))
        · obtain ⟨rk, hk, rfl⟩ := Option.map_eq_some_iff.mp hr
          simp only [NFProg.leakRunM, Expr.denoteM_option_eq_some, Option.bind_some, hden, hlk]
          exact rel_map_ev (R := fun a a' => a = laneOuts j rk.1 _ a') _
            (ih _ rk hk _ _ (hρ.cons false _ _ rfl))
  | forLoop count inits body k ihb ihk =>
      intro Δ ρ r hr V W hρ
      simp only [liftP] at hr
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
        simp only [NFProg.leakRunM, castRes]
        rw [show HasWord64.toNat (d := jasminTileDialect) (c'.lookup W) =
          HasWord64.toNat (d := jasminDialect) (count.lookup V) from
            congrArg BitVec.toNat hcnt]
        exact rel_bind_map (RA := fun a a' => a = laneOuts j rmb _ a')
          (RB := fun a a' => a = laneOuts j rk.1 _ a')
          (c := fun a => NFProg.leakRunM M fuel k (hvAppend a V))
          (c' := fun a' => NFProg.leakRunM (scalarTileLeak jasminDialect M) fuel rk.2
            (hvAppend a' W))
          (fun a b => .trip _ :: (a ++ b))
          (NFProg.forIterLeak_rel_bisim (R := fun a a' => a = laneOuts j rmb _ a')
            (step := fun i acc => NFProg.leakRunM M fuel body
              (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)))
            (step' := fun i acc => NFProg.leakRunM (scalarTileLeak jasminDialect M) fuel body'
              (hvAppend acc (.cons (HasWord64.ofNat (d := jasminTileDialect) i) W))) _
            (fun i _ a a' haa => by
              subst haa
              exact ihb _ ⟨rmb, body'⟩ hb _ _
                ((hρ.cons false (t := .reg 64) (BitVec.ofNat 64 i) _ rfl).app rmb _ a')) _ _
            (retArgs_sound hρ inits ⟨rmb, inits'⟩ hi))
          (fun a a' haa => by
            subst haa
            exact ihk _ rk hk _ _ (hρ.app rmb _ a'))
      · cases hr
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ρ r hr V W hρ
      simp only [liftP] at hr
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
        simp only [NFProg.leakRunM, castRes]
        rw [show HasBoolBit.toBool (d := jasminTileDialect) (c'.lookup W) =
          HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) from
            congrArg (fun b : BitVec 1 => decide (b = 1#1)) hcnd]
        refine rel_bind_map (RA := fun a a' => a = laneOuts j rme _ a')
          (RB := fun a a' => a = laneOuts j rk.1 _ a')
          (c := fun a => NFProg.leakRunM M fuel k (hvAppend a V))
          (c' := fun a' => NFProg.leakRunM (scalarTileLeak jasminDialect M) fuel rk.2
            (hvAppend a' W))
          (fun a b => .branch _ :: (a ++ b)) ?_
          (fun a a' haa => by
            subst haa
            exact ihk _ rk hk _ _ (hρ.app rme _ a'))
        split
        · exact iht _ ⟨rme, thn'⟩ ht _ _ hρ
        · exact ihe _ ⟨rme, els'⟩ he _ _ hρ
      · cases hr
  | whileLoop inits body k ihb ihk =>
      intro Δ ρ r hr V W hρ
      simp only [liftP] at hr
      obtain ⟨ri, hi, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨rb, hb, hr⟩ := Option.bind_eq_some_iff.mp hr
      split at hr
      · rename_i h
        obtain ⟨rk, hk, rfl⟩ := Option.map_eq_some_iff.mp hr
        obtain ⟨rmb, body'⟩ := rb
        obtain ⟨cm, inits'⟩ := ri
        dsimp only at h hb hk
        subst h
        simp only [NFProg.leakRunM, castRes]
        exact rel_bind_map (RA := fun a a' => a = laneOuts j cm _ a')
          (RB := fun a a' => a = laneOuts j rk.1 _ a')
          (c := fun a => NFProg.leakRunM M fuel k (hvAppend a V))
          (c' := fun a' => NFProg.leakRunM (scalarTileLeak jasminDialect M) fuel rk.2
            (hvAppend a' W))
          (fun a b => a ++ b)
          (NFProg.whileIterLeak_rel_bisim (R := fun a a' => a = laneOuts j cm _ a')
            (step := fun acc => NFProg.leakRunM M fuel body (hvAppend acc V))
            (step' := fun acc => NFProg.leakRunM (scalarTileLeak jasminDialect M) fuel body'
              (hvAppend acc W))
            (fun a a' haa => by
              subst haa
              refine rel_mono ?_ (ihb _ ⟨false :: cm, body'⟩ hb _ _ (hρ.app cm _ a'))
              rintro r r' ⟨h1, h2⟩
              rw [laneOuts_cons] at h1
              exact ⟨by rw [h1]; rfl, by rw [h1]; rfl, h2⟩) fuel _ _
            (retArgs_sound hρ inits ⟨cm, inits'⟩ hi))
          (fun a a' haa => by
            subst haa
            exact ihk _ rk hk _ _ (hρ.app cm _ a'))
      · cases hr
  | call f args k ih =>
      intro Δ ρ r hr V W hρ
      cases hr

end Sound

/-! ## 5. The lane theorems -/

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
        q W) := by
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hh
    obtain ⟨rm', q'⟩ := r
    dsimp only at hh
    subst hh
    cases h
    exact liftP_leakRun M hM fuel j p _ _ hr _ _ (EnvRel.ofMask j m Γ W)
  · cases h

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
      p.denote fuel (laneOuts j m Γ W) := by
  have h1 := laneLift_leakRun quietModel (fun _ _ => rfl) fuel j m rm p q h W
  have hs := NFProg.leakRunM_fst quietModel fuel p (laneOuts j m Γ W)
  have ht := NFProg.leakRunM_fst (scalarTileLeak jasminDialect quietModel) fuel q W
  change _ = p.denote fuel _ at hs
  change _ = scalarTileDenP jasminDialect (instDialectDenoteMOptionOfPure jasminDialect)
    fuel q W at ht
  rw [← hs, ← ht]
  exact rel_fst h1

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
      (scalarSem fuel Γ ts) (tileSem fuel (liftTys n w m Γ) (liftTys n w rm ts)) where
  relIn V W := V = laneOuts j m Γ W
  relOut o o' := o = laneOuts j rm ts o'
  sound := by
    intro p q V W o hf hVW hd
    subst hVW
    have h1 := laneLift_denote fuel j m rm p q hf W
    rw [show p.denote fuel (laneOuts j m Γ W) = some o from hd] at h1
    obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.mp h1
    exact ⟨o', ho', rfl⟩

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
      (tileLeakSem M fuel (liftTys n w m Γ) (liftTys n w rm ts)).twoRun where
  relIn V W := V.1 = laneOuts j m Γ W.1 ∧ V.2 = laneOuts j m Γ W.2
  relOut a b := b = a
  sound := by
    intro p q V W o hf hVW hd
    obtain ⟨V1, V2⟩ := V
    obtain ⟨h1, h2⟩ := hVW
    dsimp only at h1 h2
    subst h1 h2
    refine ⟨o, ?_, rfl⟩
    have e1 := laneLift_events M hM fuel j m rm p q hf W.1
    have e2 := laneLift_events M hM fuel j m rm p q hf W.2
    simp only [LeakSem.twoRun, scalarLeakSem, tileLeakSem] at hd ⊢
    rw [e1, e2]
    exact hd

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
  simp [laneLift, liftP, accLoop, tileOp?, Env.ofMask, Env.app, Env.cons, LVar.ofTag, LVar.wk,
    castRes]
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
