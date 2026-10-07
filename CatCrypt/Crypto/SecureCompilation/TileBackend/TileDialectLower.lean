/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.TileDialectModelTie
public import CatCrypt.Crypto.SecureCompilation.VIR.TileDialectModelTie
public meta import CatCrypt.Crypto.SecureCompilation.TileBackend.ComToTileIR
public import CatCrypt.Crypto.SecureCompilation.TileBackend.ComToTileIR
import Std.Data.String.ToNat

/-!
# Lowering the tile `Com` dialect to the tile model

A straight-line `Com tileDialect Γ (.tile n w)` program lowers to a block of
`TileModel.TileOp`s over named registers. The binding made in context `Γ` writes
the register `nm Γ.length`, where `nm : Nat → String` names de Bruijn levels, so
a variable keeps its register when later bindings extend the context. An op whose
shape is not `(n, w)` makes the lowering `none`.

## Main results

* `lowerCom` — the lowering, `Option (List TileOp × String)` (block and result
  register).
* `lowerCom_correct` — for every injective `nm`, every program, and every state
  holding the input valuation at the registers of its levels (`Holds`), running
  the lowered block leaves `Com.denote` in the result register.
* `bbMulTileCom` — the BabyBear Barrett multiply as a `Com tileDialect` program;
  `bbMulTileCom_denote`: its denotation is `bbMulWord` in every lane, for every
  lane count.
* `bbMulTileCom_lowered_denote` — the lowered block, run from `bbMulInit a b`,
  leaves `bbMulWord (a i) (b i)` in lane `i` of the result register;
  `bbMulTileCom_lower_isSome` — the lowering succeeds at every lane count.
* `bbMulTileComIR` — the `cuda_tile` MLIR text of the 8-lane lowered block,
  printed by `emitTileFunc`.

## Scope

The correctness theorem is stated over `TileModel.runTileBlock`. No theorem here
relates the text printed by `emitTileFunc` to `TileModel`, and `emitTileFunc`
prints the tile type `!cuda_tile.tile<8xi64>` whatever `(n, w)` the block was
lowered at.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.TileBackend.TileDialectLower

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect (TileTy tileDialect TileImmOp)
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialectModelTie (toTileOp toImmTileOp)
open CatCrypt.Crypto.SecureCompilation.TileBackend.TileModel
  (Tile TileState evalTileOp runTileBlock bbMulWord bbMulInit)
open CatCrypt.Crypto.SecureCompilation.TileBackend.ComToTileIR (emitTileFunc)
open Ctxt (Var)

/-! ## 1. Register names -/

/-- The de Bruijn level of a variable: `here` in `t :: Γ` has level `Γ.length`,
    and `there v` has the level of `v`. A binding keeps its level when the
    context is extended. -/
def varLevel {Γ : Ctxt tileDialect} {t : TileTy} : Var Γ t → Nat
  | @Var.here _ Γ _ => Γ.length
  | .there v => varLevel v

/-- The level of a variable of `Γ` is below `Γ.length`. -/
theorem varLevel_lt {Γ : Ctxt tileDialect} {t : TileTy} (v : Var Γ t) :
    varLevel v < Γ.length := by
  induction v with
  | here => simp [varLevel]
  | there v ih => simp only [varLevel, List.length_cons]; omega

/-! ## 2. The lowering -/

/-- Lower one `tileDialect` expression at shape `n × w` to one model op writing
    register `d`; an operand variable `v` is read from register `nm (varLevel v)`.
    `none` when the op's shape is not `(n, w)`. -/
def lowerExpr (n w : Nat) (nm : Nat → String) (d : String) {Γ : Ctxt tileDialect}
    {t : TileTy} : Expr tileDialect Γ t → Option TileModel.TileOp
  | ⟨.tileBin op n' w', _, .cons x (.cons y .nil)⟩ =>
      if n' = n ∧ w' = w then some (toTileOp op d (nm (varLevel x)) (nm (varLevel y)))
      else none
  | ⟨.tilePermute n' w', _, .cons idx (.cons a .nil)⟩ =>
      if n' = n ∧ w' = w then some (.permxv d (nm (varLevel idx)) (nm (varLevel a)))
      else none
  | ⟨.tileBroadcast n' w' k, _, .cons a .nil⟩ =>
      if n' = n ∧ w' = w then some (.bcast d (nm (varLevel a)) k) else none
  | ⟨.tileReduce n' w', _, .cons a .nil⟩ =>
      if n' = n ∧ w' = w then some (.hadd d (nm (varLevel a))) else none
  | ⟨.tileConst n' w' k, _, .nil⟩ =>
      if n' = n ∧ w' = w then some (.const d k) else none
  | ⟨.tileShiftImm op n' w' k, _, .cons a .nil⟩ =>
      if n' = n ∧ w' = w then some (toImmTileOp op d (nm (varLevel a)) k) else none
  | ⟨.tileMulhu n' w', _, .cons x (.cons y .nil)⟩ =>
      if n' = n ∧ w' = w then some (.mulhu d (nm (varLevel x)) (nm (varLevel y))) else none
  | ⟨.tileShuffle n' w' idx, _, .cons x (.cons y .nil)⟩ =>
      if n' = n ∧ w' = w then some (.shuffle d (nm (varLevel x)) (nm (varLevel y)) idx)
      else none
  | ⟨.tileBlend n' w' mask, _, .cons x (.cons y .nil)⟩ =>
      if n' = n ∧ w' = w then some (.blend d (nm (varLevel x)) (nm (varLevel y)) mask)
      else none

/-- Lower a straight-line `tileDialect` program at shape `n × w`: the binding made
    in context `Γ` writes register `nm Γ.length`, and the result is the register
    of the returned variable. -/
def lowerCom (n w : Nat) (nm : Nat → String) :
    {Γ : Ctxt tileDialect} → {t : TileTy} → Com tileDialect Γ t →
      Option (List TileModel.TileOp × String)
  | _, _, .ret v => some ([], nm (varLevel v))
  | Γ, _, .var e body =>
      (lowerExpr n w nm (nm Γ.length) e).bind fun op =>
        (lowerCom n w nm body).map fun p => (op :: p.1, p.2)

/-! ## 3. Correctness -/

/-- The state `s` holds the valuation `V`: every variable of type `tile n w` sits
    in the register named by its level. -/
def Holds {n w : Nat} (nm : Nat → String) (s : TileState n w) {Γ : Ctxt tileDialect}
    (V : Ctxt.Valuation Γ) : Prop :=
  ∀ v : Var Γ (.tile n w), s.get (nm (varLevel v)) = v.lookup V

/-- An expression that lowers at shape `(n, w)` has type `tile n w`. -/
theorem lowerExpr_ty {n w : Nat} {nm : Nat → String} {d : String} {Γ : Ctxt tileDialect}
    {t : TileTy} {e : Expr tileDialect Γ t} {op : TileModel.TileOp}
    (h : lowerExpr n w nm d e = some op) : t = .tile n w := by
  obtain ⟨op', hret, args⟩ := e
  subst hret
  cases op' <;> rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [lowerExpr] at h <;>
    (split_ifs at h with hc; obtain ⟨rfl, rfl⟩ := hc; rfl)

/-- The op a lowered expression produces writes only its destination register. -/
theorem lowerExpr_frame {n w : Nat} {nm : Nat → String} {d : String} {Γ : Ctxt tileDialect}
    {t : TileTy} {e : Expr tileDialect Γ t} {op : TileModel.TileOp}
    (h : lowerExpr n w nm d e = some op) (s : TileState n w) (r : String) (hr : r ≠ d) :
    (evalTileOp s op).get r = s.get r := by
  obtain ⟨op', hret, args⟩ := e
  subst hret
  cases op' <;> rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [lowerExpr] at h <;>
    (split_ifs at h with hc; cases h)
  all_goals first
    | (simp [evalTileOp, TileModel.TileState.set, TileModel.TileState.get, hr]; done)
    | (rename_i iop _ _ _
       cases (iop : TileImmOp) <;> simp [evalTileOp, toImmTileOp, TileModel.TileState.set,
         TileModel.TileState.get, hr])
    | (rename_i bop _ _
       cases (bop : JasminBinOp) <;> simp [evalTileOp, toTileOp, TileModel.TileState.set,
         TileModel.TileState.get, hr])

/-- **One lowered expression.** From a state holding `V`, the op a `tile n w`
    expression lowers to writes the expression's denotation into its destination
    register. Each arm is a tie of `TileDialectModelTie`. -/
theorem lowerExpr_correct {n w : Nat} {nm : Nat → String} {d : String} {Γ : Ctxt tileDialect}
    (s : TileState n w) (V : Ctxt.Valuation Γ) (hs : Holds nm s V)
    (e : Expr tileDialect Γ (.tile n w)) {op : TileModel.TileOp}
    (h : lowerExpr n w nm d e = some op) :
    (evalTileOp s op).get d = e.denote V := by
  obtain ⟨op', hret, args⟩ := e
  cases op' <;> cases hret <;> rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [lowerExpr, and_self, if_true, Option.some.injEq] at h <;> subst h
  all_goals first
    | (rw [TileDialectModelTie.tileBin_eq_evalTileOp, hs x, hs y]; rfl)
    | (rw [← TileDialectModelTie.tilePermute_denote_eq_evalTileOp, hs x, hs y]; rfl)
    | (rw [← TileDialectModelTie.tileBroadcast_denote_eq_evalTileOp, hs x]; rfl)
    | (rw [← TileDialectModelTie.tileReduce_denote_eq_evalTileOp, hs x]; rfl)
    | (rw [← TileDialectModelTie.tileConst_denote_eq_evalTileOp]; rfl)
    | (rw [← TileDialectModelTie.tileShiftImm_denote_eq_evalTileOp, hs x]; rfl)
    | (rw [← TileDialectModelTie.tileMulhu_denote_eq_evalTileOp, hs x, hs y]; rfl)
    | (rw [← TileDialectModelTie.tileShuffle_denote_eq_evalTileOp, hs x, hs y]; rfl)
    | (rw [← TileDialectModelTie.tileBlend_denote_eq_evalTileOp, hs x, hs y]; rfl)

/-- Extending the valuation by `x`: a state that holds `x` in register
    `nm Γ.length` and agrees with a state holding `V` elsewhere holds `V.extend x`,
    for injective `nm`. -/
theorem Holds.cons {n w : Nat} {nm : Nat → String} (hnm : Function.Injective nm)
    {Γ : Ctxt tileDialect} {s s' : TileState n w} {V : Ctxt.Valuation Γ}
    (hs : Holds nm s V) (x : Tile n w) (hx : s'.get (nm Γ.length) = x)
    (hfr : ∀ r, r ≠ nm Γ.length → s'.get r = s.get r) :
    Holds nm s' (V.extend x : Ctxt.Valuation (TileTy.tile n w :: Γ)) := by
  intro v
  cases v with
  | here => exact hx
  | there v =>
    show s'.get (nm (varLevel v)) = v.lookup V
    rw [hfr _ (fun h => absurd (hnm h) (Nat.ne_of_lt (varLevel_lt v)))]
    exact hs v

/-- **Correctness of the lowering.** For an injective register naming `nm`, every
    straight-line program `c : Com tileDialect Γ (.tile n w)` whose lowering is
    `some (blk, r)`, and every state `s` holding the valuation `V`, running `blk`
    from `s` leaves `c.denote V` in register `r`. -/
theorem lowerCom_correct {n w : Nat} {nm : Nat → String} (hnm : Function.Injective nm) :
    ∀ {Γ : Ctxt tileDialect} (c : Com tileDialect Γ (.tile n w)) (s : TileState n w)
      (V : Ctxt.Valuation Γ), Holds nm s V →
      ∀ {blk : List TileModel.TileOp} {r : String}, lowerCom n w nm c = some (blk, r) →
      (runTileBlock s blk).get r = c.denote V
  | _, .ret v, s, V, hs, blk, r, h => by
    simp only [lowerCom, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hs v
  | Γ, .var e body, s, V, hs, blk, r, h => by
    cases he : lowerExpr n w nm (nm Γ.length) e with
    | none => simp [lowerCom, he] at h
    | some op =>
      have ht := lowerExpr_ty he
      subst ht
      cases hb : lowerCom n w nm body with
      | none => simp [lowerCom, he, hb] at h
      | some p =>
        simp only [lowerCom, he, hb, Option.bind_some, Option.map_some,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact lowerCom_correct hnm body (evalTileOp s op) (V.extend (e.denote V))
          (Holds.cons hnm hs _ (lowerExpr_correct s V hs e he)
            (fun r hr => lowerExpr_frame he s r hr)) hb

/-! ## 4. The BabyBear multiply through the dialect -/

/-- `tileBin op` at shape `n × w` on two variables. -/
def binE {Γ : Ctxt tileDialect} (op : JasminBinOp) {n w : Nat}
    (x y : Var Γ (.tile n w)) : Expr tileDialect Γ (.tile n w) :=
  ⟨.tileBin op n w, rfl, .cons x (.cons y .nil)⟩

/-- `tileConst` at shape `n × w`. -/
def constE {Γ : Ctxt tileDialect} (n w k : Nat) : Expr tileDialect Γ (.tile n w) :=
  ⟨.tileConst n w k, rfl, .nil⟩

/-- Denotation of `binE`: the lane-wise `JasminBinOp.apply`. -/
theorem binE_denote {Γ : Ctxt tileDialect} (op : JasminBinOp) {n w : Nat}
    (x y : Var Γ (.tile n w)) (V : Ctxt.Valuation Γ) :
    (binE op x y).denote V = fun i => op.apply (x.lookup V i) (y.lookup V i) :=
  rfl

/-- Denotation of `constE`: the lane-uniform `BitVec.ofNat w k`. -/
theorem constE_denote {Γ : Ctxt tileDialect} (n w k : Nat) (V : Ctxt.Valuation Γ) :
    (constE n w k).denote V = fun _ => BitVec.ofNat w k :=
  rfl

/-- Lane `i` of `here` looked up in `x :: V` is lane `i` of `x`. Stated over
    `HVector` at index type `TileTy`, the form in which `simp` meets the
    valuations of a concrete program. -/
theorem lookup_here {Γ : List TileTy} {m u : Nat} (x : Tile m u)
    (V : HVector (fun t : TileTy => (⟦t⟧ : Type)) Γ) (i : Fin m) :
    (Var.here : Var (d := tileDialect) (TileTy.tile m u :: Γ) (.tile m u)).lookup
      (@HVector.cons TileTy (fun t : TileTy => (⟦t⟧ : Type)) _ _ x V) i = x i :=
  rfl

/-- Lane `i` of `there v` looked up in `x :: V` is lane `i` of `v` in `V`. -/
theorem lookup_there {Γ : List TileTy} {m u : Nat} {s : TileTy}
    (v : Var (d := tileDialect) Γ (TileTy.tile m u)) (x : ⟦s⟧)
    (V : HVector (fun t : TileTy => (⟦t⟧ : Type)) Γ) (i : Fin m) :
    (Var.there v : Var (d := tileDialect) (s :: Γ) (TileTy.tile m u)).lookup
      (@HVector.cons TileTy (fun t : TileTy => (⟦t⟧ : Type)) _ _ x V) i = v.lookup V i :=
  rfl

/-- `Com.denote` of a binding. -/
theorem denote_var {Γ : Ctxt tileDialect} {t u : TileTy} (e : Expr tileDialect Γ t)
    (body : Com tileDialect (t :: Γ) u) (V : Ctxt.Valuation Γ) :
    (Com.var e body).denote V = body.denote (.cons (e.denote V) V) :=
  rfl

/-- `Com.denote` of a return. -/
theorem denote_ret {Γ : Ctxt tileDialect} {t : TileTy} (v : Var Γ t)
    (V : Ctxt.Valuation Γ) : (Com.ret v).denote V = v.lookup V :=
  rfl

/-- The BabyBear Barrett multiply `bbMulWord` as a `Com tileDialect` program over
    two input tiles `a` (variable `here`) and `b`, in the op order of
    `TileModel.bbMulReg`. Each comment lists the context, newest binding first. -/
def bbMulTileCom (n : Nat) : Com tileDialect [.tile n 64, .tile n 64] (.tile n 64) :=
  -- MU, P, zero, c30, c32, c63
  .var (constE n 64 2290649223) <|
  .var (constE n 64 2013265921) <|
  .var (constE n 64 0) <|
  .var (constE n 64 30) <|
  .var (constE n 64 32) <|
  .var (constE n 64 63) <|
  -- x := a * b   (ctx: c63 c32 c30 zero P MU a b)
  .var (binE .mul (.there (.there (.there (.there (.there (.there .here))))))
      (.there (.there (.there (.there (.there (.there (.there .here)))))))) <|
  -- q := x >>> c30   (ctx: x c63 c32 c30 ...)
  .var (binE .shr .here (.there (.there (.there .here)))) <|
  -- q := q * MU   (ctx: q x c63 c32 c30 zero P MU ...)
  .var (binE .mul .here
      (.there (.there (.there (.there (.there (.there (.there .here)))))))) <|
  -- q := q >>> c32   (ctx: q q x c63 c32 ...)
  .var (binE .shr .here (.there (.there (.there (.there .here))))) <|
  -- q := q * P   (ctx: q q q x c63 c32 c30 zero P ...)
  .var (binE .mul .here
      (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) <|
  -- x := x - q   (ctx: q q q q x ...)
  .var (binE .sub (.there (.there (.there (.there .here)))) .here) <|
  -- o := x - P   (ctx: x q q q q x c63 c32 c30 zero P ...)
  .var (binE .sub .here
      (.there (.there (.there (.there (.there (.there (.there (.there (.there
        (.there .here))))))))))) <|
  -- m := o >>> c63   (ctx: o x q q q q x c63 ...)
  .var (binE .shr .here (.there (.there (.there (.there (.there (.there (.there
      .here)))))))) <|
  -- m := zero - m   (ctx: m o x q q q q x c63 c32 c30 zero ...)
  .var (binE .sub
      (.there (.there (.there (.there (.there (.there (.there (.there (.there
        (.there (.there .here)))))))))))
      .here) <|
  -- m := m &&& P   (ctx: m m o x q q q q x c63 c32 c30 zero P ...)
  .var (binE .and .here
      (.there (.there (.there (.there (.there (.there (.there (.there (.there
        (.there (.there (.there (.there .here)))))))))))))) <|
  -- o := o + m   (ctx: m m m o ...)
  .var (binE .add (.there (.there (.there .here))) .here) <|
  .ret .here

/-- **The dialect program computes `bbMulWord` on every lane**, for any lane
    count `n`. -/
theorem bbMulTileCom_denote {n : Nat} (a b : Tile n 64) :
    (bbMulTileCom n).denote (.cons a (.cons b .nil)) = fun i => bbMulWord (a i) (b i) := by
  funext i
  simp only [bbMulTileCom, denote_var, denote_ret, binE_denote, constE_denote, lookup_here,
    lookup_there, JasminBinOp.apply, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    bbMulWord]

/-- Register names for the lowering of `bbMulTileCom`: level `1` (input `a`) is
    `"a"`, level `0` (input `b`) is `"b"`, and level `k + 2` is `"t" ++ toString k`.
    The input names are the ones `emitTileFunc` binds. -/
def bbName : Nat → String
  | 0 => "b"
  | 1 => "a"
  | k + 2 => "t" ++ toString k

/-- A string starting with `t` differs from a string whose first character is
    not `t`. -/
theorem t_append_ne {s c : String} (hc : c.toList.head? ≠ some 't') : "t" ++ s ≠ c := by
  intro h
  apply hc
  rw [← h]
  simp

/-- `bbName` is injective. -/
theorem bbName_injective : Function.Injective bbName := by
  intro i j h
  match i, j with
  | 0, 0 => rfl
  | 1, 1 => rfl
  | 0, 1 => simp [bbName] at h
  | 1, 0 => simp [bbName] at h
  | k + 2, 0 => exact absurd h (t_append_ne (by decide))
  | k + 2, 1 => exact absurd h (t_append_ne (by decide))
  | 0, k + 2 => exact absurd h.symm (t_append_ne (by decide))
  | 1, k + 2 => exact absurd h.symm (t_append_ne (by decide))
  | k + 2, l + 2 =>
    simp only [bbName] at h
    rw [Nat.repr_injective ((String.append_right_inj "t").mp h)]

/-- `TileModel.bbMulInit a b` holds the input valuation `⟨a, b⟩` under `bbName`. -/
theorem holds_bbMulInit {n : Nat} (a b : Tile n 64) :
    Holds bbName (bbMulInit a b)
      (.cons a (.cons b .nil) :
        Ctxt.Valuation (d := tileDialect) [TileTy.tile n 64, TileTy.tile n 64]) := by
  intro v
  rcases v with _ | _ | ⟨_ | _⟩
  · rfl
  · rfl

/-- The lowering of `bbMulTileCom` succeeds at every lane count. -/
theorem bbMulTileCom_lower_isSome (n : Nat) :
    (lowerCom n 64 bbName (bbMulTileCom n)).isSome = true := by
  simp [lowerCom, lowerExpr, bbMulTileCom, binE, constE]

/-- **The lowered BabyBear multiply computes `bbMulWord` on every lane.** Running
    the block the lowering produces for `bbMulTileCom n` from the state holding
    `a` in `"a"` and `b` in `"b"` leaves `bbMulWord (a i) (b i)` in lane `i` of
    the result register. -/
theorem bbMulTileCom_lowered_denote {n : Nat} (a b : Tile n 64)
    {blk : List TileModel.TileOp} {r : String}
    (h : lowerCom n 64 bbName (bbMulTileCom n) = some (blk, r)) :
    (runTileBlock (bbMulInit a b) blk).get r = fun i => bbMulWord (a i) (b i) :=
  (lowerCom_correct bbName_injective _ _ _ (holds_bbMulInit a b) h).trans
    (bbMulTileCom_denote a b)

/-- The BabyBear multiply emitted as `cuda_tile` MLIR through the dialect: the
    8-lane `bbMulTileCom` lowered by `lowerCom` and printed by `emitTileFunc`. -/
def bbMulTileComIR : String :=
  match lowerCom 8 64 bbName (bbMulTileCom 8) with
  | some (blk, r) => emitTileFunc "bb_mul_tile_com" blk r
  | none => ""

end CatCrypt.Crypto.SecureCompilation.TileBackend.TileDialectLower

end
