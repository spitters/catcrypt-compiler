/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.TileLegal
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapNF
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVecCore

/-!
# Lane lifting followed by tile legalisation

For a target `T : TileTarget jasminDialect` of `T.laneCount` lanes of `T.laneBits` bits, a
scalar structured program `p` is lifted to the tile level by `LaneMapNF.laneLift` along a
mask and then legalised by `TileLegal.legalise T`. The result is a program of
`jasminDialect` on registers of the shape. `readOuts T j` reads lane `j` of a valuation of
the legalised context: the lane read `T.lane` at a register that holds a tile, and the
value at a scalar.

## Main definitions

* `readTy`, `readOuts` — lane `j` of a legalised value and of a legalised valuation.
* `unpackTy`, `unpackOuts` — the tile valuation a legalised valuation is the packing of.
* `tileLegalLaneCert` — the step certificate of the composed step at lane `j`.

## Main results

* `tileLegal_laneLift_denote` — lane `j` of the results of the lifted and legalised program
  is the result of the scalar program on lane `j` of the inputs, at every fuel and every
  valuation of the legalised context.
* `tileLegal_laneLift_leakRun` — the scalar run on lane `j` and the run of the lifted and
  legalised program both fail, or both succeed with the lane-`j` results and equal events.
* `tileLegal_laneLift_laneMapVec` — for a straight-line program covered by a `LaneShape`,
  lane `j` of the lifted and legalised program is lane `k` of `laneMapVec S c` at inputs
  with equal lanes: both are the scalar denotation on that lane
  (`LaneMapVec.laneMapVec_denote`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.TileLegalLaneMap

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapNF
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
open CatCrypt.Crypto.SecureCompilation.VIR.TileLegal
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open Ctxt (Var Valuation)

variable (T : TileTarget jasminDialect)

/-! ## 1. Lanes of a legalised valuation -/

/-- Lane `j` of a legalised value: the lane of a register that holds a tile, and the value
    of a scalar. -/
def readTy (j : Fin T.laneCount) (b : Bool) (t : JasminTy) :
    ⟦legalTy T (liftTy T.laneCount T.laneBits b t)⟧ → ⟦t⟧ :=
  match b with
  | true => fun x => laneRd j t (T.lane x)
  | false => fun x => x

/-- Lane `j` of a legalised valuation. -/
def readOuts (j : Fin T.laneCount) : (rm : List Bool) → (ts : List JasminTy) →
    Valuation (d := jasminDialect) ((liftTys T.laneCount T.laneBits rm ts).map (legalTy T)) →
    Valuation (d := jasminDialect) ts
  | _, [], _ => .nil
  | rm, t :: ts, .cons x xs =>
      .cons (readTy T j (rm.headD false) t x) (readOuts j rm.tail ts xs)

/-- The lifted value a legalised value is the packing of. -/
def unpackTy (b : Bool) (t : JasminTy) :
    ⟦legalTy T (liftTy T.laneCount T.laneBits b t)⟧ →
      ⟦liftTy T.laneCount T.laneBits b t⟧ :=
  match b with
  | true => fun x => T.lane x
  | false => fun x => x

/-- The tile valuation a legalised valuation is the packing of. -/
def unpackOuts : (rm : List Bool) → (ts : List JasminTy) →
    Valuation (d := jasminDialect) ((liftTys T.laneCount T.laneBits rm ts).map (legalTy T)) →
    Valuation (d := jasminTileDialect) (liftTys T.laneCount T.laneBits rm ts)
  | _, [], _ => .nil
  | rm, t :: ts, .cons x xs =>
      .cons (unpackTy T (rm.headD false) t x) (unpackOuts rm.tail ts xs)

/-- Lane `j` of a packed value is lane `j` of the value. -/
theorem readTy_pack (j : Fin T.laneCount) (b : Bool) (t : JasminTy)
    (x : ⟦liftTy T.laneCount T.laneBits b t⟧) :
    readTy T j b t (packTy T x) = outRd j b t x := by
  cases b
  · rfl
  · show laneRd j t (T.lane (T.pack _ x)) = laneRd j t x
    congr 1
    funext k
    exact T.lane_pack x k

/-- A legalised value is the packing of `unpackTy` of it. -/
theorem pack_unpackTy (b : Bool) (t : JasminTy)
    (x : ⟦legalTy T (liftTy T.laneCount T.laneBits b t)⟧) :
    packTy T (unpackTy T b t x) = x := by
  cases b
  · rfl
  · exact T.pack_lane x

/-- Lane `j` of a packed valuation is lane `j` of the valuation. -/
theorem readOuts_pack (j : Fin T.laneCount) : (rm : List Bool) → (ts : List JasminTy) →
    (o : Valuation (d := jasminTileDialect) (liftTys T.laneCount T.laneBits rm ts)) →
    readOuts T j rm ts (packOuts T o) = laneOuts j rm ts o
  | _, [], .nil => rfl
  | rm, t :: ts, .cons x xs =>
      congrArg₂ HVector.cons (readTy_pack T j (rm.headD false) t x)
        (readOuts_pack j rm.tail ts xs)

/-- A legalised valuation is the packing of `unpackOuts` of it. -/
theorem pack_unpackOuts : (rm : List Bool) → (ts : List JasminTy) →
    (W : Valuation (d := jasminDialect)
      ((liftTys T.laneCount T.laneBits rm ts).map (legalTy T))) →
    packOuts T (unpackOuts T rm ts W) = W
  | _, [], .nil => rfl
  | rm, t :: ts, .cons x xs =>
      congrArg₂ HVector.cons (pack_unpackTy T (rm.headD false) t x)
        (pack_unpackOuts rm.tail ts xs)

/-! ## 2. The composed lane theorems -/

/-- **Lane lifting followed by legalisation computes the scalar program on every lane.**
    For a lifting `q` of `p` and a legalisation `r` of `q` at the target `T`, lane `j` of
    the results of `r` on a valuation `W` of the legalised context is the result of `p` on
    lane `j` of `W`, at every fuel. -/
theorem tileLegal_laneLift_denote (fuel : Nat) (j : Fin T.laneCount) (m rm : List Bool)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (q : NFProg jasminTileDialect (liftTys T.laneCount T.laneBits m Γ)
      (liftTys T.laneCount T.laneBits rm ts))
    (r : NFProg jasminDialect ((liftTys T.laneCount T.laneBits m Γ).map (legalTy T))
      ((liftTys T.laneCount T.laneBits rm ts).map (legalTy T)))
    (hq : laneLift T.laneCount T.laneBits m rm p = some q) (hr : legalise T q = some r)
    (W : Valuation (d := jasminDialect)
      ((liftTys T.laneCount T.laneBits m Γ).map (legalTy T))) :
    (r.denote fuel W).map (readOuts T j rm ts) = p.denote fuel (readOuts T j m Γ W) := by
  rw [← pack_unpackOuts T m Γ W]
  generalize unpackOuts T m Γ W = U
  have h1 : r.denote fuel (packOuts T U) = _ := tileLegal_denote T fuel q r hr U
  rw [h1, Option.map_map, readOuts_pack, ← laneLift_denote fuel j m rm p q hq U]
  congr 1
  funext o
  exact readOuts_pack T j rm ts o

/-- **Lane lifting followed by legalisation preserves runs and events at every lane.** In a
    leakage model in which the blocks of `T` and the lifted scalar operations are quiet,
    the run of `p` on lane `j` of `W` and the run of `r` on `W` both fail, or both succeed
    with lane `j` of the results of `r` equal to the results of `p` and with equal
    events. -/
theorem tileLegal_laneLift_leakRun {M : LeakModel jasminDialect} (hQ : T.Quiet M)
    (hM : LaneQuiet T.laneBits M) (fuel : Nat) (j : Fin T.laneCount) (m rm : List Bool)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (q : NFProg jasminTileDialect (liftTys T.laneCount T.laneBits m Γ)
      (liftTys T.laneCount T.laneBits rm ts))
    (r : NFProg jasminDialect ((liftTys T.laneCount T.laneBits m Γ).map (legalTy T))
      ((liftTys T.laneCount T.laneBits rm ts).map (legalTy T)))
    (hq : laneLift T.laneCount T.laneBits m rm p = some q) (hr : legalise T q = some r)
    (W : Valuation (d := jasminDialect)
      ((liftTys T.laneCount T.laneBits m Γ).map (legalTy T))) :
    Option.Rel (fun a a' => a.1 = readOuts T j rm ts a'.1 ∧ a.2 = a'.2)
      (NFProg.leakRunM M fuel p (readOuts T j m Γ W)) (NFProg.leakRun M fuel r W) := by
  rw [← pack_unpackOuts T m Γ W]
  generalize unpackOuts T m Γ W = U
  have h1 : NFProg.leakRun M fuel r (packOuts T U) = _ := tileLegal_leakRun hQ fuel q r hr U
  have h2 := laneLift_leakRun M hM fuel j m rm p q hq U
  rw [h1, readOuts_pack]
  revert h2
  generalize scalarTileLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) M
    fuel q U = o2
  generalize NFProg.leakRunM M fuel p (laneOuts j m Γ U) = o1
  intro h2
  cases h2 with
  | none => exact .none
  | some h => exact .some ⟨h.1.trans (readOuts_pack T j rm ts _).symm, h.2⟩

open PassChain in
/-- **The certificate of lane lifting followed by legalisation at lane `j`.** The step from
    the semantics of scalar programs to that of programs of `jasminDialect` on registers of
    the shape: the input relation holds of a scalar valuation and a valuation of the
    legalised context when the first is lane `j` of the second, and the output relation
    likewise of the result tuples. -/
def tileLegalLaneCert (j : Fin T.laneCount) (m rm : List Bool) (fuel : Nat)
    (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    StepCert
      (fun p : NFProg jasminDialect Γ ts =>
        (laneLift T.laneCount T.laneBits m rm p).bind (legalise T))
      (scalarSem fuel Γ ts)
      (targetSem jasminDialect fuel ((liftTys T.laneCount T.laneBits m Γ).map (legalTy T))
        ((liftTys T.laneCount T.laneBits rm ts).map (legalTy T))) where
  relIn V W := V = readOuts T j m Γ W
  relOut o o' := o = readOuts T j rm ts o'
  sound := by
    intro p r V W o hf hVW hd
    subst hVW
    obtain ⟨q, hq, hr⟩ := Option.bind_eq_some_iff.mp hf
    have h := tileLegal_laneLift_denote T fuel j m rm p q r hq hr W
    rw [show p.denote fuel (readOuts T j m Γ W) = some o from hd] at h
    obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨o', ho', rfl⟩

/-! ## 3. Agreement with `laneMapVec` -/

/-- **Agreement with `laneMapVec` on straight-line programs.** Let `c` be a straight-line
    program covered by the lane shape `S` (without a high multiply), `q` a lifting of its
    embedding `NFProg.ofCom c` and `r` a legalisation of `q` at `T`. At a valuation `W₁` of
    the widened context of `S` and a valuation `W₂` of the legalised context whose lanes
    `k` and `j` agree, lane `j` of the result of `r` is lane `k` of the value of
    `laneMapVec S c`. Both sides are the denotation of `c` on that lane, by
    `tileLegal_laneLift_denote` and `laneMapVec_denote`. -/
theorem tileLegal_laneLift_laneMapVec (S : LaneShape) (hm : S.mulhiExpr = none)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) (hc : S.Covered c)
    (k : Fin S.laneCount) (j : Fin T.laneCount) (m rm : List Bool)
    (q : NFProg jasminTileDialect (liftTys T.laneCount T.laneBits m Γ)
      (liftTys T.laneCount T.laneBits rm [t]))
    (r : NFProg jasminDialect ((liftTys T.laneCount T.laneBits m Γ).map (legalTy T))
      ((liftTys T.laneCount T.laneBits rm [t]).map (legalTy T)))
    (hq : laneLift T.laneCount T.laneBits m rm (NFProg.ofCom c) = some q)
    (hr : legalise T q = some r) (fuel : Nat) (W₁ : Valuation (S.widenCtxt Γ))
    (W₂ : Valuation (d := jasminDialect)
      ((liftTys T.laneCount T.laneBits m Γ).map (legalTy T)))
    (hW : S.laneOf k Γ W₁ = readOuts T j m Γ W₂) :
    (r.denote fuel W₂).map (readOuts T j rm [t]) =
      some (.cons (S.laneOfTy k t ((laneMapVec S c).denote W₁)) .nil) := by
  rw [tileLegal_laneLift_denote T fuel j m rm _ q r hq hr W₂, ← hW, NFProg.denote_ofCom,
    laneMapVec_denote_default S hm c hc W₁ k]

end CatCrypt.Crypto.SecureCompilation.VIR.TileLegalLaneMap
