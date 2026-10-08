/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapNF
public import CatCrypt.Crypto.SecureCompilation.VIR.SelLegal
public import CatCrypt.Crypto.Optimizer.Rewrite.RangeSelNF

/-!
# Lane lifting of the selection dialect

`selLane n w` is the lane-operation table (`LaneMapNF.LaneTable`) of the scalar dialect
`SelDialect.jasminSel` into `tileSel jasminVec`, the source dialect of the legalisation
`SelLegal.legaliseSel`. Its type alphabet is `JasminTy` beside the tile types, so it is the
dialect `tileSide SelDialect.jasminSel VecSelOp` and no relabelling stands between the lifting and the
legalisation. The table extends `jasminLane`: a scalar operation of `jasminDialect` has the
tile expression `tileOp?` gives it, `umin w` becomes `tileMinu n w` and `mulu w` becomes
`tileMulu n w`. A scalar operation of `jasminDialect` on scalar operands is kept; `umin` and
`mulu` on scalar operands are refused, since `tileSel jasminVec` has no scalar form of them.

The composition takes a scalar program `p` of `jasminDialect` through the range-conditioned
selections `rangeSel a`, the lifting `selLaneLift` and the legalisation `legaliseSel S` at a
gate `S` of a lane shape `T` of `jasminVec`.

## Main definitions

* `scalarEnv`, `vecExpr`: an environment and a tile-side expression of `jasminDialect` read
  in the selection dialects.
* `selTileOp?`, `selIsLane`, `selLane`: the table.
* `selLaneLift`: the lifting of a program of `jasminSel` at the table.
* `selLaneLiftCert`, `selLaneLiftLeakCert`: its step certificates at a lane.
* `laneOfLegal`, `lanesOfLegal`, `tileOfLegal`, `tilesOfLegal`: a lane and the tile of a
  legalised value and valuation, over every scalar dialect and lane shape.

## Main results

* `selLane_sound`: the laws of the table at a leakage model of `jasminDialect`.
* `selLaneLift_denote`: lane `j` of the denotation of the lifted program is the denotation
  of the program of `jasminSel` on lane `j`.
* `selLaneLift_leakRun`, `selLaneLift_events`: the runs agree at every lane with equal
  events.
* `rangeSel_lift_legal_denote`: for `p` of `jasminDialect`, lane `j` of the results of the
  legalised lifting of `rangeSel a p` is the result of `p` on lane `j`.
* `rangeSel_lift_legal_leakRun`: the same for runs with events.
* `rangeSel_lift_qword_denote`, `rangeSel_lift_dword_denote`: the instances at eight 64-bit
  lanes and at sixteen 32-bit lanes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneMapSel

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapNF
open CatCrypt.Crypto.SecureCompilation.VIR.SelDialect
open CatCrypt.Crypto.SecureCompilation.VIR.SelLegal
open CatCrypt.Crypto.SecureCompilation.VIR.TileLegal
open CatCrypt.Crypto.SecureCompilation.VIR.TileSelectX86
open CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum
  (castVar castArgs lookup_castVar lookupArgs_castArgs)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.RangeDomain (umin)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop (CarriedAnn)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeSelNF
  (rangeSel rangeSel_denote rangeSel_leakRun offsetCondAdd)
open Ctxt (Var Valuation)

/-- The operations of `tileSel jasminVec`. -/
abbrev VecSelOp : Type := (tileSel jasminVec).Op

/-- The denotation of `tileSel jasminVec` over the pure denotation of `jasminVec`. -/
@[instance_reducible] def vecSelDenote : DialectDenoteM (tileSel jasminVec) Option :=
  tileSelDenote jasminVec (instDialectDenoteMOptionOfPure jasminVec)

attribute [local instance] vecSelDenote jasminTileDenote tileSideWord64 tileSideBoolBit

/-! ## 1. Environments and expressions of `jasminDialect` in the selection dialects -/

section Embed

variable {n w : Nat} {Γ : Ctxt SelDialect.jasminSel} {Δ : Ctxt (tileSide SelDialect.jasminSel VecSelOp)}

/-- An environment of `jasminSel` into `tileSel jasminVec`, read as an environment of
    `jasminDialect` into `jasminTileDialect`. -/
def scalarEnv (ρ : LaneEnv SelDialect.jasminSel VecSelOp n w Γ Δ) : Env n w Γ Δ :=
  fun t v => ⟨((ρ t (castVar v)).sc).map castVar, ((ρ t (castVar v)).ln).map castVar⟩

/-- The reading of an environment keeps the lane relation. -/
theorem scalarEnv_rel {ρ : LaneEnv SelDialect.jasminSel VecSelOp n w Γ Δ}
    {V : Valuation (d := SelDialect.jasminSel) Γ} {W : Valuation Δ} {j : Fin n}
    (hρ : LaneRel (laneRd j) ρ V W) : EnvRel j (scalarEnv ρ) V W := by
  intro t v
  refine ⟨fun v' hv => ?_, fun v' hv => ?_⟩
  · obtain ⟨v₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hv
    exact (lookup_castVar (O' := Sum JasminOp TileOp) v₀ W).trans
      (((hρ t (castVar v)).1 v₀ h₀).trans (lookup_castVar v V))
  · obtain ⟨v₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hv
    exact (congrArg (laneRd j t) (lookup_castVar (O' := Sum JasminOp TileOp) v₀ W)).trans
      (((hρ t (castVar v)).2 v₀ h₀).trans (lookup_castVar v V))

/-- `unmapInl` depends on the type alphabet of the scalar dialect only. -/
theorem unmapInl_ops {O O' A : Type} [TyDenote A] : ∀ {ts : List A}
    (x : HVector (fun t => ⟦t⟧) (ts.map (Sum.inl (β := TileTy)))),
    unmapInl (d := ⟨O, A⟩) (e := tileDialect) x = unmapInl (d := ⟨O', A⟩) (e := tileDialect) x
  | [], _ => rfl
  | t :: _, .cons x xs => by
      show HVector.cons (f := fun t : A => ⟦t⟧) (t := t) x
          (unmapInl (d := ⟨O, A⟩) (e := tileDialect) xs) =
        HVector.cons (f := fun t : A => ⟦t⟧) (t := t) x
          (unmapInl (d := ⟨O', A⟩) (e := tileDialect) xs)
      rw [unmapInl_ops (O := O) (O' := O') xs]

/-- `unmapInr` depends on the type alphabet of the scalar dialect only. -/
theorem unmapInr_ops {O O' A : Type} [TyDenote A] : ∀ {ts : List TileTy}
    (x : HVector (fun t => ⟦t⟧) (ts.map (Sum.inr (α := A)))),
    unmapInr (d := ⟨O, A⟩) (e := tileDialect) x = unmapInr (d := ⟨O', A⟩) (e := tileDialect) x
  | [], _ => rfl
  | t :: _, .cons x xs => by
      show HVector.cons (f := fun t : TileTy => ⟦t⟧) (t := t) x
          (unmapInr (d := ⟨O, A⟩) (e := tileDialect) xs) =
        HVector.cons (f := fun t : TileTy => ⟦t⟧) (t := t) x
          (unmapInr (d := ⟨O', A⟩) (e := tileDialect) xs)
      rw [unmapInr_ops (O := O) (O' := O') xs]

/-- An expression of `jasminTileDialect` as an expression of `tileSel jasminVec`: a scalar
    operation in the scalar summand of `jasminVec`, a tile operation in the tile summand. -/
def vecExpr {Δ : List (JasminTy ⊕ TileTy)} {t : JasminTy ⊕ TileTy}
    (e : Expr jasminTileDialect Δ t) : Expr (tileSel jasminVec) Δ t :=
  match e with
  | ⟨.inl o, h, as⟩ => ⟨.inl (.inl (.inl o)), h, castArgs as⟩
  | ⟨.inr o, h, as⟩ => ⟨.inl (.inr o), h, castArgs as⟩

/-- An embedded expression denotes as the expression. -/
theorem vecExpr_denoteM {Δ : List (JasminTy ⊕ TileTy)} {t : JasminTy ⊕ TileTy}
    (e : Expr jasminTileDialect Δ t) (W : Valuation (d := jasminTileDialect) Δ) :
    Expr.denoteM (M := Option) (vecExpr e) W = e.denoteM (M := Option) W := by
  obtain ⟨op, rfl, args⟩ := e
  rcases op with o | o
  · show (scalarTileDenote jasminVec (instDialectDenoteMOptionOfPure jasminVec)).denoteM
        (.inl (.inl o)) (Expr.lookupArgs (d := tileSel jasminVec) (castArgs args) W) = _
    rw [lookupArgs_castArgs args W]
    exact congrArg (fun a => some (DialectDenote.denote (d := jasminDialect) o a))
      (unmapInl_ops (O := jasminVec.Op) (O' := JasminOp) (Expr.lookupArgs args W))
  · show (scalarTileDenote jasminVec (instDialectDenoteMOptionOfPure jasminVec)).denoteM
        (.inr o) (Expr.lookupArgs (d := tileSel jasminVec) (castArgs args) W) = _
    rw [lookupArgs_castArgs args W]
    exact congrArg (fun a => some (DialectDenote.denote (d := tileDialect) o a))
      (unmapInr_ops (O := jasminVec.Op) (O' := JasminOp) (Expr.lookupArgs args W))

/-- An embedded expression emits the events of the expression. -/
theorem vecExpr_ctLeak (M : LeakModel jasminDialect) {Δ : List (JasminTy ⊕ TileTy)}
    {t : JasminTy ⊕ TileTy} (e : Expr jasminTileDialect Δ t)
    (W : Valuation (d := jasminTileDialect) Δ) :
    Expr.ctLeak (tileSelLeak jasminVec (jasminVecLeak M)) (vecExpr e) W =
      Expr.ctLeak (scalarTileLeak jasminDialect M) e W := by
  obtain ⟨op, rfl, args⟩ := e
  rcases op with o | o
  · show opLeak (tileSelLeak jasminVec (jasminVecLeak M)) (.inl (.inl (.inl o)))
        (Expr.lookupArgs (d := tileSel jasminVec) (castArgs args) W) =
      opLeak (scalarTileLeak jasminDialect M) (.inl o) (Expr.lookupArgs args W)
    rw [lookupArgs_castArgs args W, tileSel_opLeak_inl, scalarTile_opLeak_inl,
      scalarTile_opLeak_inl, unmapInl_ops (O := jasminVec.Op) (O' := JasminOp)]
    exact jasminVec_opLeak_inl M o _
  · show opLeak (tileSelLeak jasminVec (jasminVecLeak M)) (.inl (.inr o))
        (Expr.lookupArgs (d := tileSel jasminVec) (castArgs args) W) =
      opLeak (scalarTileLeak jasminDialect M) (.inr o) (Expr.lookupArgs args W)
    rw [lookupArgs_castArgs args W, tileSel_opLeak_inl, scalarTile_opLeak_inr,
      scalarTile_opLeak_inr]

end Embed

/-! ## 2. The table -/

section Table

variable (n w : Nat)

/-- The operations of `jasminSel` with a tile counterpart at lane width `w`: those of
    `isLaneOp`, and `umin` and `mulu` at width `w`. -/
def selIsLane : JasminOp ⊕ SelOp → Bool
  | .inl o => isLaneOp w o
  | .inr (.umin w') => decide (w' = w)
  | .inr (.mulu w') => decide (w' = w)

/-- The tile expression of an operation of `jasminSel` at width `w` whose operands have tile
    forms: `tileOp?` on an operation of `jasminDialect`, `tileMinu` on `umin` and `tileMulu`
    on `mulu`. -/
def selTileOp? {Γ : Ctxt SelDialect.jasminSel} {Δ : Ctxt (tileSide SelDialect.jasminSel VecSelOp)}
    (ρ : LaneEnv SelDialect.jasminSel VecSelOp n w Γ Δ) :
    (op : JasminOp ⊕ SelOp) → HVector (fun t => Var Γ t) (DialectSignature.sig op) →
    Option (Expr (tileSel jasminVec) Δ (Sum.inr (TileTy.tile n w)))
  | .inl o, args => (tileOp? n w (scalarEnv ρ) o (castArgs args)).map vecExpr
  | .inr (.umin w'), args =>
      if w' = w then
        (ρ _ args.head).ln.bind fun a => (ρ _ args.tail.head).ln.map fun b =>
          ⟨.inr (.tileMinu n w), rfl, .cons a (.cons b .nil)⟩
      else none
  | .inr (.mulu w'), args =>
      if w' = w then
        (ρ _ args.head).ln.bind fun a => (ρ _ args.tail.head).ln.map fun b =>
          ⟨.inr (.tileMulu n w), rfl, .cons a (.cons b .nil)⟩
      else none

/-- The value of a constant operation of `jasminSel` at width `w`. -/
def selConst? : JasminOp ⊕ SelOp → Option Nat
  | .inl o => constOf? w o
  | .inr _ => none

/-- A scalar operation of `jasminSel` on scalar forms in `tileSel jasminVec`: an operation
    of `jasminDialect` in the scalar summand of `jasminVec`; `umin` and `mulu` have no scalar
    form there. -/
def selKeep? : (op : JasminOp ⊕ SelOp) → {t : JasminTy} →
    DialectSignature.ret (d := SelDialect.jasminSel) op = t →
    {Δ : Ctxt (tileSide SelDialect.jasminSel VecSelOp)} →
    HVector (fun u => Var Δ u)
      ((DialectSignature.sig (d := SelDialect.jasminSel) op).map (Sum.inl (β := TileTy))) →
    Option (Expr (tileSel jasminVec) Δ (Sum.inl t))
  | .inl o, _, h, _, as => some ⟨.inl (.inl (.inl o)), congrArg Sum.inl h, as⟩
  | .inr _, _, _, _, _ => none

/-- **The lane-operation table of `jasminSel`** into `tileSel jasminVec`: the table
    `jasminLane` on the operations of `jasminDialect`, with `umin w ↦ tileMinu n w` and
    `mulu w ↦ tileMulu n w`. -/
@[reducible] def selLane : LaneTable SelDialect.jasminSel VecSelOp n w where
  rd := laneRd
  isLane := selIsLane w
  tile := selTileOp? n w
  const := selConst? w
  constE := fun c => ⟨.inl (.inr (.tileConst n w c)), rfl, .nil⟩
  keep := selKeep?

variable {n w}

/-- **The laws of `selLane`** at a leakage model `M` of `jasminDialect`: the scalar side
    has the model `jasminSelLeak M`, the tile side the model of `tileSel jasminVec` over
    `jasminVecLeak M`. -/
theorem selLane_sound (M : LeakModel jasminDialect) :
    (selLane n w).Sound (jasminSelLeak M) (tileSelLeak jasminVec (jasminVecLeak M)) where
  tile := by
    intro Γ Δ ρ V W j hρ op args e' h
    rcases op with o | o
    · obtain ⟨e₀, he₀, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hl, x', hx', hlane, hleak⟩ :=
        tileOp?_sound M (scalarEnv_rel hρ) o (castArgs args) e₀ he₀
      rw [lookupArgs_castArgs args V] at hlane
      exact ⟨hl, x', (vecExpr_denoteM e₀ W).trans hx', congrArg some hlane.symm,
        (vecExpr_ctLeak M e₀ W).trans hleak⟩
    · cases o with
      | umin w' =>
          simp only [selTileOp?] at h
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
                have h1 : laneRd j (.reg _) (a.lookup W) = x.lookup V := (hρ _ x).2 a ha
                have h2 : laneRd j (.reg _) (b.lookup W) = y.lookup V := (hρ _ y).2 b hb
                rw [laneRd_reg] at h1 h2
                refine ⟨by simp [selIsLane], _, rfl, ?_, rfl⟩
                show some (umin (x.lookup V) (y.lookup V)) = some (laneRd j (.reg _) _)
                rw [laneRd_reg, ← h1, ← h2]
                rfl
          · cases h
      | mulu w' =>
          simp only [selTileOp?] at h
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
                have h1 : laneRd j (.reg _) (a.lookup W) = x.lookup V := (hρ _ x).2 a ha
                have h2 : laneRd j (.reg _) (b.lookup W) = y.lookup V := (hρ _ y).2 b hb
                rw [laneRd_reg] at h1 h2
                refine ⟨by simp [selIsLane], _, rfl, ?_, rfl⟩
                show some (halfProd (x.lookup V) (y.lookup V)) = some (laneRd j (.reg _) _)
                rw [laneRd_reg, ← h1, ← h2]
                rfl
          · cases h
  const := by
    intro j op c h vals x hx
    rcases op with o | o
    · cases hx
      exact constOf?_lane j o c h vals
    · cases h
  constE_denote := fun _ _ _ => rfl
  constE_leak := fun _ _ _ => rfl
  keep := by
    intro op Δ as e' W h
    rcases op with o | o
    · cases h
      refine ⟨congrArg (fun a => some (DialectDenote.denote (d := jasminDialect) o a))
        (unmapInl_ops (O := jasminVec.Op) (O' := SelDialect.jasminSel.Op)
          (Expr.lookupArgs as W)), ?_⟩
      show opLeak (tileSelLeak jasminVec (jasminVecLeak M)) (.inl (.inl (.inl o))) _ =
        opLeak (jasminSelLeak M) (.inl o) _
      rw [tileSel_opLeak_inl, scalarTile_opLeak_inl, jasminSel_opLeak_inl,
        unmapInl_ops (O := jasminVec.Op) (O' := SelDialect.jasminSel.Op)]
      exact jasminVec_opLeak_inl M o _
    · cases h

/-- In a model in which the operations of `isLaneOp` are quiet, the operations of
    `selIsLane` are quiet in `jasminSelLeak`. -/
theorem selIsLane_quiet {M : LeakModel jasminDialect} (hM : LaneQuiet w M) :
    ∀ op, (selLane n w).isLane op = true → (jasminSelLeak M).kind op = .quiet := by
  intro op h
  rcases op with o | o
  · exact hM o h
  · rfl

end Table

/-! ## 3. The lifting and its theorems -/

section Lift

variable (n w : Nat)

/-- **Lane lifting of a program of `jasminSel`** into `tileSel jasminVec` at the table
    `selLane`, with the entry mask `m` and the result mask `rm`. -/
def selLaneLift (m rm : List Bool) {Γ : Ctxt SelDialect.jasminSel} {ts : List JasminTy}
    (p : NFProg SelDialect.jasminSel Γ ts) :
    Option (NFProg vecTileSel (markTys n w m Γ) (markTys n w rm ts)) :=
  tableLift (selLane n w) m rm p

variable {n w}

/-- **Lane lifting of the selection dialect preserves runs at every lane.** The run of `p`
    on lane `j` of `W` and the run of the lifted program on `W` both fail, or both succeed
    with lane `j` of the lifted results equal to the results of `p` and equal events. -/
theorem selLaneLift_leakRun (M : LeakModel jasminDialect) (hM : LaneQuiet w M) (fuel : Nat)
    (j : Fin n) (m rm : List Bool) {Γ : Ctxt SelDialect.jasminSel} {ts : List JasminTy}
    (p : NFProg SelDialect.jasminSel Γ ts) (q : NFProg vecTileSel (markTys n w m Γ) (markTys n w rm ts))
    (h : selLaneLift n w m rm p = some q)
    (W : Valuation (d := vecTileSel) (markTys n w m Γ)) :
    Option.Rel (fun b b' => b.1 = readMarks (laneRd j) rm ts b'.1 ∧ b.2 = b'.2)
      (NFProg.leakRunM (jasminSelLeak M) fuel p (readMarks (laneRd j) m Γ W))
      (tileSelLeakRun jasminVec (instDialectDenoteMOptionOfPure jasminVec) (jasminVecLeak M)
        fuel q W) :=
  tableLift_leakRun (selLane n w) (jasminSelLeak M) (tileSelLeak jasminVec (jasminVecLeak M))
    (selLane_sound M) (selIsLane_quiet hM) fuel j m rm p q h W

/-- **The events of a lifted run** are the events of the run of `p` on each lane. -/
theorem selLaneLift_events (M : LeakModel jasminDialect) (hM : LaneQuiet w M) (fuel : Nat)
    (j : Fin n) (m rm : List Bool) {Γ : Ctxt SelDialect.jasminSel} {ts : List JasminTy}
    (p : NFProg SelDialect.jasminSel Γ ts) (q : NFProg vecTileSel (markTys n w m Γ) (markTys n w rm ts))
    (h : selLaneLift n w m rm p = some q)
    (W : Valuation (d := vecTileSel) (markTys n w m Γ)) :
    (tileSelLeakRun jasminVec (instDialectDenoteMOptionOfPure jasminVec) (jasminVecLeak M)
        fuel q W).map Prod.snd =
      (NFProg.leakRunM (jasminSelLeak M) fuel p (readMarks (laneRd j) m Γ W)).map Prod.snd :=
  tableLift_events (selLane n w) (jasminSelLeak M) (tileSelLeak jasminVec (jasminVecLeak M))
    (selLane_sound M) (selIsLane_quiet hM) fuel j m rm p q h W

/-- **The lane theorem of the selection dialect.** Lane `j` of the denotation of the lifted
    program on a tile valuation `W` is the denotation of `p` on lane `j` of `W`, at every
    fuel. -/
theorem selLaneLift_denote (fuel : Nat) (j : Fin n) (m rm : List Bool)
    {Γ : Ctxt SelDialect.jasminSel} {ts : List JasminTy} (p : NFProg SelDialect.jasminSel Γ ts)
    (q : NFProg vecTileSel (markTys n w m Γ) (markTys n w rm ts))
    (h : selLaneLift n w m rm p = some q)
    (W : Valuation (d := vecTileSel) (markTys n w m Γ)) :
    (tileSelDenP jasminVec (instDialectDenoteMOptionOfPure jasminVec) fuel q W).map
        (readMarks (laneRd j) rm ts) =
      p.denote fuel (readMarks (laneRd j) m Γ W) :=
  tableLift_denote (selLane n w) (jasminSelLeak quietModel)
    (tileSelLeak jasminVec (jasminVecLeak quietModel)) (selLane_sound quietModel)
    (selIsLane_quiet (M := quietModel) (fun _ _ => rfl)) fuel j m rm p q h W

open PassChain in
/-- **The certificate of lane lifting of the selection dialect at lane `j`.** The input
    relation holds of a scalar valuation and a tile valuation when the first is lane `j` of
    the second, and the output relation likewise of the result tuples. -/
def selLaneLiftCert (j : Fin n) (m rm : List Bool) (fuel : Nat) (Γ : Ctxt SelDialect.jasminSel)
    (ts : List JasminTy) :
    StepCert (selLaneLift n w m rm (Γ := Γ) (ts := ts)) (denoteSem SelDialect.jasminSel fuel Γ ts)
      (tileSelSem jasminVec fuel (markTys n w m Γ) (markTys n w rm ts)) :=
  tableLiftCert (selLane n w) (jasminSelLeak quietModel)
    (tileSelLeak jasminVec (jasminVecLeak quietModel)) (selLane_sound quietModel)
    (selIsLane_quiet (M := quietModel) (fun _ _ => rfl)) j m rm fuel Γ ts

open PassChain in
/-- **The leakage certificate of lane lifting of the selection dialect at lane `j`**,
    between the two-run semantics of the events of the two dialects. -/
def selLaneLiftLeakCert (M : LeakModel jasminDialect) (hM : LaneQuiet w M) (j : Fin n)
    (m rm : List Bool) (fuel : Nat) (Γ : Ctxt SelDialect.jasminSel) (ts : List JasminTy) :
    StepCert (selLaneLift n w m rm (Γ := Γ) (ts := ts))
      (eventSem (jasminSelLeak M) fuel Γ ts).twoRun
      (eventSem (d := vecTileSel) (tileSelLeak jasminVec (jasminVecLeak M)) fuel
        (markTys n w m Γ) (markTys n w rm ts)).twoRun :=
  tableLiftLeakCert (selLane n w) (jasminSelLeak M)
    (tileSelLeak jasminVec (jasminVecLeak M)) (selLane_sound M) (selIsLane_quiet hM) j m rm
    fuel Γ ts

end Lift

/-! ## 4. Lanes of a legalised valuation -/

section Legal

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
  (T : TileTarget d) (r : (t : d.Ty) → (Fin T.laneCount → BitVec T.laneBits) → ⟦t⟧)

/-- The scalar value of a legalised value along the reading `r` of a tile: the reading of
    the lanes of a register that holds a tile, and the value of a scalar. -/
def laneOfLegal (b : Bool) (t : d.Ty) :
    ⟦legalTy T (markTy T.laneCount T.laneBits b t)⟧ → ⟦t⟧ :=
  match b with
  | true => fun x => r t (T.lane x)
  | false => fun x => x

/-- The scalar valuation of a legalised valuation along the reading `r`. -/
def lanesOfLegal : (rm : List Bool) → (ts : List d.Ty) →
    Valuation (d := d) ((markTys T.laneCount T.laneBits rm ts).map (legalTy T)) →
    Valuation (d := d) ts
  | _, [], _ => .nil
  | rm, t :: ts, .cons x xs =>
      .cons (laneOfLegal T r (rm.headD false) t x) (lanesOfLegal rm.tail ts xs)

/-- The marked value a legalised value is the packing of. -/
def tileOfLegal (b : Bool) (t : d.Ty) :
    ⟦legalTy T (markTy T.laneCount T.laneBits b t)⟧ →
      ⟦markTy T.laneCount T.laneBits b t⟧ :=
  match b with
  | true => fun x => T.lane x
  | false => fun x => x

/-- The marked valuation a legalised valuation is the packing of. -/
def tilesOfLegal : (rm : List Bool) → (ts : List d.Ty) →
    Valuation (d := d) ((markTys T.laneCount T.laneBits rm ts).map (legalTy T)) →
    Valuation (d := scalarTile d) (markTys T.laneCount T.laneBits rm ts)
  | _, [], _ => .nil
  | rm, t :: ts, .cons x xs =>
      .cons (tileOfLegal T (rm.headD false) t x) (tilesOfLegal rm.tail ts xs)

/-- The scalar value of a packed value is the reading of the value. -/
theorem laneOfLegal_pack (b : Bool) (t : d.Ty) (x : ⟦markTy T.laneCount T.laneBits b t⟧) :
    laneOfLegal T r b t (packTy T x) = readMark r b t x := by
  cases b
  · rfl
  · show r t (T.lane (T.pack _ x)) = r t x
    congr 1
    funext k
    exact T.lane_pack x k

/-- A legalised value is the packing of `tileOfLegal` of it. -/
theorem pack_tileOfLegal (b : Bool) (t : d.Ty)
    (x : ⟦legalTy T (markTy T.laneCount T.laneBits b t)⟧) :
    packTy T (tileOfLegal T b t x) = x := by
  cases b
  · rfl
  · exact T.pack_lane x

/-- The scalar valuation of a packed valuation is the reading of the valuation. -/
theorem lanesOfLegal_pack : (rm : List Bool) → (ts : List d.Ty) →
    (o : Valuation (d := scalarTile d) (markTys T.laneCount T.laneBits rm ts)) →
    lanesOfLegal T r rm ts (packOuts T o) = readMarks r rm ts o
  | _, [], .nil => rfl
  | rm, t :: ts, .cons x xs =>
      congrArg₂ HVector.cons (laneOfLegal_pack T r (rm.headD false) t x)
        (lanesOfLegal_pack rm.tail ts xs)

/-- A legalised valuation is the packing of `tilesOfLegal` of it. -/
theorem pack_tilesOfLegal : (rm : List Bool) → (ts : List d.Ty) →
    (W : Valuation (d := d) ((markTys T.laneCount T.laneBits rm ts).map (legalTy T))) →
    packOuts T (tilesOfLegal T rm ts W) = W
  | _, [], .nil => rfl
  | rm, t :: ts, .cons x xs =>
      congrArg₂ HVector.cons (pack_tileOfLegal T (rm.headD false) t x)
        (pack_tilesOfLegal rm.tail ts xs)

end Legal

/-! ## 5. The composition with the range stage and the legalisation -/

section Compose

variable {T : TileTarget jasminVec}

/-- **Selection, lifting and legalisation compute the scalar program on every lane.** For
    a program `p` of `jasminDialect`, a lifting `q` of `rangeSel a p` and a legalisation `r`
    of `q` at the gate `S` of the shape `T`: lane `j` of the results of `r` on a valuation
    `W` of the legalised context is the result of `p` on lane `j` of `W`, at every fuel. -/
theorem rangeSel_lift_legal_denote (S : SelTarget T) (a : CarriedAnn) (fuel : Nat)
    (j : Fin T.laneCount) (m rm : List Bool) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts)
    (q : NFProg vecTileSel (markTys T.laneCount T.laneBits m Γ)
      (markTys T.laneCount T.laneBits rm ts))
    (r : NFProg jasminVec ((markTys T.laneCount T.laneBits m Γ).map (legalTy T))
      ((markTys T.laneCount T.laneBits rm ts).map (legalTy T)))
    (hq : selLaneLift T.laneCount T.laneBits m rm (rangeSel a p) = some q)
    (hr : legaliseSel S q = some r)
    (W : Valuation (d := jasminVec) ((markTys T.laneCount T.laneBits m Γ).map (legalTy T))) :
    (r.denote fuel W).map (lanesOfLegal T (laneRd j) rm ts) =
      p.denote fuel (lanesOfLegal T (laneRd j) m Γ W) := by
  rw [← pack_tilesOfLegal T m Γ W]
  generalize tilesOfLegal T m Γ W = U
  have h1 : r.denote fuel (packOuts T U) = _ := selLegal_denote S fuel q r hr U
  rw [h1, Option.map_map, lanesOfLegal_pack, ← rangeSel_denote a p fuel,
    ← selLaneLift_denote fuel j m rm (rangeSel a p) q hq U]
  congr 1
  funext o
  exact lanesOfLegal_pack T (laneRd j) rm ts o

/-- **Selection, lifting and legalisation preserve runs and events at every lane.** In a
    model `M` of `jasminDialect` in which the `regArith` operations and the lifted scalar
    operations are quiet and over which the blocks of `T` and `S` are quiet: the run of `p`
    on lane `j` of `W` and the run of `r` on `W` both fail, or both succeed with lane `j` of
    the results of `r` equal to the results of `p` and with equal events. -/
theorem rangeSel_lift_legal_leakRun {S : SelTarget T} {M : LeakModel jasminDialect}
    (hT : T.Quiet (jasminVecLeak M)) (hS : S.Quiet (jasminVecLeak M))
    (hA : ∀ bop w, M.kind (.regArith bop w) = .quiet) (hM : LaneQuiet T.laneBits M)
    (a : CarriedAnn) (fuel : Nat) (j : Fin T.laneCount) (m rm : List Bool)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (q : NFProg vecTileSel (markTys T.laneCount T.laneBits m Γ)
      (markTys T.laneCount T.laneBits rm ts))
    (r : NFProg jasminVec ((markTys T.laneCount T.laneBits m Γ).map (legalTy T))
      ((markTys T.laneCount T.laneBits rm ts).map (legalTy T)))
    (hq : selLaneLift T.laneCount T.laneBits m rm (rangeSel a p) = some q)
    (hr : legaliseSel S q = some r)
    (W : Valuation (d := jasminVec) ((markTys T.laneCount T.laneBits m Γ).map (legalTy T))) :
    Option.Rel (fun b b' => b.1 = lanesOfLegal T (laneRd j) rm ts b'.1 ∧ b.2 = b'.2)
      (NFProg.leakRun M fuel p (lanesOfLegal T (laneRd j) m Γ W))
      (NFProg.leakRun (jasminVecLeak M) fuel r W) := by
  rw [← pack_tilesOfLegal T m Γ W]
  generalize tilesOfLegal T m Γ W = U
  have h1 : NFProg.leakRun (jasminVecLeak M) fuel r (packOuts T U) = _ :=
    selLegal_leakRun hT hS fuel q r hr U
  have h2 := selLaneLift_leakRun M hM fuel j m rm (rangeSel a p) q hq U
  rw [NFProg.leakRunM_eq_leakRun, rangeSel_leakRun hA] at h2
  rw [h1, lanesOfLegal_pack]
  revert h2
  generalize tileSelLeakRun jasminVec (instDialectDenoteMOptionOfPure jasminVec)
    (jasminVecLeak M) fuel q U = o2
  generalize NFProg.leakRun M fuel p (readMarks (laneRd j) m Γ U) = o1
  intro h2
  cases h2 with
  | none => exact .none
  | some h => exact .some ⟨h.1.trans (lanesOfLegal_pack T (laneRd j) rm ts _).symm, h.2⟩

/-- **The composition at eight 64-bit lanes**, with `tileMinu` as `vpminuq` and `tileMulu`
    as `vpmuludq`. -/
theorem rangeSel_lift_qword_denote (a : CarriedAnn) (fuel : Nat) (j : Fin 8)
    (m rm : List Bool) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts)
    (q : NFProg vecTileSel (markTys 8 64 m Γ) (markTys 8 64 rm ts))
    (r : NFProg jasminVec ((markTys 8 64 m Γ).map (legalTy selQ))
      ((markTys 8 64 rm ts).map (legalTy selQ)))
    (hq : selLaneLift 8 64 m rm (rangeSel a p) = some q) (hr : legaliseSel qwordSel q = some r)
    (W : Valuation (d := jasminVec) ((markTys 8 64 m Γ).map (legalTy selQ))) :
    (r.denote fuel W).map (lanesOfLegal selQ (laneRd j) rm ts) =
      p.denote fuel (lanesOfLegal selQ (laneRd j) m Γ W) :=
  rangeSel_lift_legal_denote qwordSel a fuel j m rm p q r hq hr W

/-- **The composition at sixteen 32-bit lanes**, with `tileMinu` as `vpminud`. -/
theorem rangeSel_lift_dword_denote (a : CarriedAnn) (fuel : Nat) (j : Fin 16)
    (m rm : List Bool) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts)
    (q : NFProg vecTileSel (markTys 16 32 m Γ) (markTys 16 32 rm ts))
    (r : NFProg jasminVec ((markTys 16 32 m Γ).map (legalTy selD))
      ((markTys 16 32 rm ts).map (legalTy selD)))
    (hq : selLaneLift 16 32 m rm (rangeSel a p) = some q)
    (hr : legaliseSel dwordSel q = some r)
    (W : Valuation (d := jasminVec) ((markTys 16 32 m Γ).map (legalTy selD))) :
    (r.denote fuel W).map (lanesOfLegal selD (laneRd j) rm ts) =
      p.denote fuel (lanesOfLegal selD (laneRd j) m Γ W) :=
  rangeSel_lift_legal_denote dwordSel a fuel j m rm p q r hq hr W

/-- **`offsetCondAdd` passes the three stages at eight 64-bit lanes.** The range stage
    replaces its conditional addition by one unsigned minimum, the lifting at the mask
    `[true]` accepts the result as `q`, `legaliseSel qwordSel` returns a program `r` of
    `jasminVec` on `q`, and lane `j` of the result of `r` on a ZMM register is the result of
    `offsetCondAdd` on lane `j` of the register, at every fuel. -/
theorem offsetCondAdd_qword :
    ∃ q r, selLaneLift 8 64 [true] [true] (rangeSel .empty offsetCondAdd) = some q ∧
      legaliseSel qwordSel q = some r ∧
      ∀ (fuel : Nat) (j : Fin 8)
        (W : Valuation (d := jasminVec)
          ((markTys 8 64 [true] [JasminTy.reg 64]).map (legalTy selQ))),
        (r.denote fuel W).map (lanesOfLegal selQ (laneRd j) [true] [.reg 64]) =
          offsetCondAdd.denote fuel (lanesOfLegal selQ (laneRd j) [true] [.reg 64] W) := by
  have h : ((selLaneLift 8 64 [true] [true] (rangeSel .empty offsetCondAdd)).bind
      (legaliseSel qwordSel)).isSome = true := by
    rfl
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨q, hq, hr⟩ := Option.bind_eq_some_iff.mp hr
  exact ⟨q, r, hq, hr, fun fuel j W =>
    rangeSel_lift_qword_denote .empty fuel j [true] [true] offsetCondAdd q r hq hr W⟩

end Compose

end CatCrypt.Crypto.SecureCompilation.VIR.LaneMapSel
