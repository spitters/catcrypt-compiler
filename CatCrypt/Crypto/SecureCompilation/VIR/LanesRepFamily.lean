/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LanesRep
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLoweringRel

/-!
# The lanes representation as a representation family

The lane programs `basemulProgW` and `accProgW` are `MultiReturnCom` programs over lane
contexts. `laneLowering` is the multi-value lowering of a source dialect whose types are
lane counts, whose values are coefficient vectors `Fin n → ZMod q` and whose ops each take
one vector argument; it maps `n` to `Ctxs w n` and each op to its lane program.
`lanesFamily` is the `RepFamily` of `LanesRep` over it, graded by a bound per lane and a
factor. The base multiplication and the row accumulation form two such lowerings,
`bmLowering` and `accLowering`, whose relational block squares follow from
`basemulProgW_rel` and `accProgW_rel`.

## Main definitions

* `LaneOps`, `laneDialect`, `laneLowering`, `lanesFamily`: the source dialect of lane ops,
  its lowering to lane programs and the representation family.
* `bmOps`, `bmLowering`, `bmXfer`: the base multiplication as lane ops, its lowering to
  `basemulProgW` and its bound transfer.
* `accOps`, `accLowering`, `accXfer`: the same for the row accumulation and `accProgW`.

## Main results

* `laneLowering_blockSquareRel`: the relational block square of a lane lowering from a
  contract per op.
* `bmLowering_blockSquareRel`, `accLowering_blockSquareRel`: the relational block squares
  of the two lowerings.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.SignedLanes

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord
open CatCrypt.Crypto.SecureCompilation.VIR.PointwiseAcc
open CatCrypt.Crypto.SecureCompilation.VIR.RingDialect (Limbs basemulF)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLoweringRel
open Finset (range)

/-! ## 1. The lane lowering and its representation family -/

/-- **Lane ops** over `ZMod q`: each op takes one coefficient vector of `arity` lanes and
returns one of `outN` lanes. -/
structure LaneOps (q : ℕ) where
  /-- The ops. -/
  Op : Type
  /-- The number of input lanes of an op. -/
  arity : Op → ℕ
  /-- The number of output lanes of an op. -/
  outN : Op → ℕ
  /-- The denotation of an op on coefficient vectors. -/
  den : (o : Op) → (Fin (arity o) → ZMod q) → Fin (outN o) → ZMod q

/-- The source dialect of lane ops: a type is a lane count. -/
def laneDialect {q : ℕ} (O : LaneOps q) : Dialect where
  Op := O.Op
  Ty := ℕ

instance {q : ℕ} (O : LaneOps q) : TyDenote (laneDialect O).Ty where
  denote n := Fin n → ZMod q

instance {q : ℕ} (O : LaneOps q) : DialectSignature (laneDialect O) where
  sig o := [O.arity o]
  ret o := O.outN o

instance {q : ℕ} (O : LaneOps q) : DialectDenote (laneDialect O) where
  denote o args := O.den o args.head

/-- **The lane lowering.** A lane count `n` lowers to the lane context `Ctxs w n` and each op
to its lane program `blk o`. -/
def laneLowering {q : ℕ} (O : LaneOps q) (w : ℕ)
    (blk : (o : O.Op) → MultiReturnCom jasminDialect (Ctxs w (O.arity o)) (Ctxs w (O.outN o))) :
    MultiBlockLoweringData (laneDialect O) jasminDialect where
  mapTys n := Ctxs w n
  lowerOp o := MultiReturnCom.rename (inlHom []) (blk o)

/-- **The lanes family.** A grade is a bound per lane and a factor; a lanes valuation is
related to a coefficient vector at a grade by `LanesRep`. -/
abbrev lanesFamily {q : ℕ} (O : LaneOps q) (w : ℕ)
    (blk : (o : O.Op) → MultiReturnCom jasminDialect (Ctxs w (O.arity o)) (Ctxs w (O.outN o))) :
    RepFamily (laneLowering O w blk) where
  G _ := (ℕ → ℕ) × ZMod q
  R g a W := LanesRep q w g.2 g.1 a W

/-- **The block square of a lane lowering.** If every lane program maps lanes related at
`g` to lanes related at `g'` whenever the transfer sends `g` to `g'`, the lowering has the
relational block square of the transfer. -/
theorem laneLowering_blockSquareRel {q : ℕ} (O : LaneOps q) (w : ℕ)
    (blk : (o : O.Op) → MultiReturnCom jasminDialect (Ctxs w (O.arity o)) (Ctxs w (O.outN o)))
    (xfer : XferOp (laneDialect O) (lanesFamily O w blk).G)
    (h : ∀ (o : O.Op) (g g' : (ℕ → ℕ) × ZMod q), xfer o (.cons g .nil) = some g' →
      ∀ (a : Fin (O.arity o) → ZMod q) (W : Valuation (Ctxs w (O.arity o))),
        LanesRep q w g.2 g.1 a W → LanesRep q w g'.2 g'.1 (O.den o a) ((blk o).denote W)) :
    (laneLowering O w blk).BlockSquareRel (lanesFamily O w blk) xfer := by
  intro o gs g hx vals W hW
  obtain ⟨A, B, rfl, hA, -⟩ := FlatRel.inv_cons (L := laneLowering O w blk)
    (F := lanesFamily O w blk) (t := O.arity o) (Γ := []) hW
  rcases gs with _ | ⟨g₀, _ | _⟩
  have e : ∀ (A' : Valuation (Ctxs w (O.arity o))) (B' : Valuation ([] : Ctxt jasminDialect)),
      (MultiReturnCom.rename (inlHom []) (blk o)).denote (hvAppend A' B') = (blk o).denote A' :=
    fun A' B' => by rw [multiReturnCom_denote_rename, pullV_inlHom]
  show LanesRep q w g.2 g.1 (O.den o vals.head)
    ((MultiReturnCom.rename (inlHom []) (blk o)).denote (hvAppend A B))
  exact (e A B) ▸ h o g₀ g hx vals.head A hA

/-! ## 2. The base multiplication -/

/-- The first half of a coefficient vector of `2 N` lanes. -/
def fstHalf {q N : ℕ} (a : Fin (2 * N) → ZMod q) : Fin N → ZMod q := fun t => a ⟨t, by omega⟩

/-- The second half of a coefficient vector of `2 N` lanes. -/
def sndHalf {q N : ℕ} (a : Fin (2 * N) → ZMod q) : Fin N → ZMod q :=
  fun t => a ⟨N + t, by omega⟩

theorem pairCoeffs_halves {q N : ℕ} (a : Fin (2 * N) → ZMod q) :
    pairCoeffs (row1 (fstHalf a)) (row1 (sndHalf a)) = a := by
  funext j
  by_cases h : (j : ℕ) < N
  · simp only [pairCoeffs, dif_pos h]
    rfl
  · simp only [pairCoeffs, dif_neg h]
    show a ⟨N + (j - N), _⟩ = a j
    congr 1
    ext
    simp only
    omega

/-- The base multiplication as lane ops: op `(ψ, logN)` maps the operand pair on
`2 · 2 ^ logN` lanes to `basemulF` at `L = logN − 1`. -/
abbrev bmOps (S : BasemulSched) : LaneOps S.q where
  Op := ℕ × ℕ
  arity o := 2 * 2 ^ o.2
  outN o := 2 ^ o.2
  den o a i := basemulF o.2 (o.2 - 1) [o.1] (row1 (fstHalf a)) (row1 (sndHalf a)) ⟨0, by simp⟩ i

/-- The lowering of the base multiplication to `basemulProgW`. -/
def bmLowering (S : BasemulSched) : MultiBlockLoweringData (laneDialect (bmOps S)) jasminDialect :=
  laneLowering (bmOps S) S.w fun o => basemulProgW S o.1 o.2

/-- The bound transfer of the base multiplication: at `logN > 0`, inputs with factor `1`
and every lane bound at most `inB` give the output bound `outB` with factor `2 ^ w`. -/
def bmXfer (S : BasemulSched) :
    XferOp (laneDialect (bmOps S)) (lanesFamily (bmOps S) S.w fun o => basemulProgW S o.1 o.2).G :=
  fun o gs =>
    if 0 < o.2 ∧ (∀ i, i < 2 * 2 ^ o.2 → gs.head.1 i ≤ S.inB) ∧ gs.head.2 = 1 then
      some (fun _ => S.outB, ((2 ^ S.w : ℕ) : ZMod S.q))
    else none

/-- **The relational block square of the base multiplication.** -/
theorem bmLowering_blockSquareRel (S : BasemulSched) (hS : S.Ok) :
    (bmLowering S).BlockSquareRel (lanesFamily (bmOps S) S.w fun o => basemulProgW S o.1 o.2)
      (bmXfer S) := by
  refine laneLowering_blockSquareRel _ _ _ _ fun o g g' hx a W hW => ?_
  have hx' : (if 0 < o.2 ∧ (∀ i, i < 2 * 2 ^ o.2 → g.1 i ≤ S.inB) ∧ g.2 = 1 then
      some ((fun _ => S.outB, ((2 ^ S.w : ℕ) : ZMod S.q)) : (ℕ → ℕ) × ZMod S.q) else none)
      = some g' := hx
  split_ifs at hx' with hc
  cases hx'
  obtain ⟨hlog, hB, hκ⟩ := hc
  rw [hκ] at hW
  have hW' : LanesRep S.q S.w 1 (fun _ => S.inB)
      (pairCoeffs (row1 (fstHalf a)) (row1 (sndHalf a))) W := by
    rw [pairCoeffs_halves]
    exact hW.mono hB
  exact basemulProgW_rel S hS o.1 o.2 hlog _ _ W hW'

/-! ## 3. The row accumulation -/

/-- The lanes `off, …, off + N − 1` of a vector, zero past its end, as one row. -/
def sliceRow {q n : ℕ} (a : Fin n → ZMod q) (off N : ℕ) : Limbs [q] N :=
  row1 fun t => finLanes a (off + t)

theorem rowCoeffs_slices {q : ℕ} (k logN : ℕ) (a : Fin (2 * k * 2 ^ logN) → ZMod q) :
    rowCoeffs k logN (fun j => sliceRow a (j * 2 ^ logN) (2 ^ logN))
      (fun j => sliceRow a (k * 2 ^ logN + j * 2 ^ logN) (2 ^ logN)) = a := by
  funext m
  have hm := m.2
  by_cases h : (m : ℕ) < k * 2 ^ logN
  · simp only [rowCoeffs, if_pos h]
    show finLanes a (m / 2 ^ logN * 2 ^ logN + m % 2 ^ logN) = a m
    rw [Nat.div_add_mod', finLanes, dif_pos hm]
  · simp only [rowCoeffs, if_neg h]
    show finLanes a (k * 2 ^ logN + (m - k * 2 ^ logN) / 2 ^ logN * 2 ^ logN
      + (m - k * 2 ^ logN) % 2 ^ logN) = a m
    rw [Nat.add_assoc, Nat.div_add_mod',Nat.add_sub_cancel' (by omega), finLanes, dif_pos hm]

/-- The row accumulation as lane ops: op `(k, ψ, logN)` maps the two rows on
`2 · k · 2 ^ logN` lanes to `∑_{j < k} basemulF` at `L = logN − 1`. -/
abbrev accOps (S : AccSched) : LaneOps S.q where
  Op := ℕ × ℕ × ℕ
  arity o := 2 * o.1 * 2 ^ o.2.2
  outN o := 2 ^ o.2.2
  den o a i := ∑ j ∈ range o.1, basemulF o.2.2 (o.2.2 - 1) [o.2.1]
    (sliceRow a (j * 2 ^ o.2.2) (2 ^ o.2.2))
    (sliceRow a (o.1 * 2 ^ o.2.2 + j * 2 ^ o.2.2) (2 ^ o.2.2)) ⟨0, by simp⟩ i

/-- The lowering of the row accumulation to `accProgW`. -/
def accLowering (S : AccSched) : MultiBlockLoweringData (laneDialect (accOps S)) jasminDialect :=
  laneLowering (accOps S) S.w fun o => accProgW S o.1 o.2.1 o.2.2

/-- The bound transfer of the row accumulation at `k` terms: at `logN > 0`, `k > 0` and
the `k` of the certificate, inputs with factor `1`, the first-row lanes at most `inA` and
the second-row lanes at most `inB` give the output bound `outB` with factor `2 ^ w`. -/
def accXfer (S : AccSched) (k : ℕ) :
    XferOp (laneDialect (accOps S))
      (lanesFamily (accOps S) S.w fun o => accProgW S o.1 o.2.1 o.2.2).G :=
  fun o gs =>
    if o.1 = k ∧ 0 < o.2.2 ∧ 0 < o.1 ∧
        (∀ i, i < 2 * o.1 * 2 ^ o.2.2 → gs.head.1 i ≤ rowBound o.1 (2 ^ o.2.2) S.inA S.inB i) ∧
        gs.head.2 = 1 then
      some (fun _ => S.outB, ((2 ^ S.w : ℕ) : ZMod S.q))
    else none

/-- **The relational block square of the row accumulation** at the `k` of the
certificate `S.Ok k`. -/
theorem accLowering_blockSquareRel (S : AccSched) (k : ℕ) (hS : S.Ok k) :
    (accLowering S).BlockSquareRel
      (lanesFamily (accOps S) S.w fun o => accProgW S o.1 o.2.1 o.2.2) (accXfer S k) := by
  refine laneLowering_blockSquareRel _ _ _ _ fun o g g' hx a W hW => ?_
  have hx' : (if o.1 = k ∧ 0 < o.2.2 ∧ 0 < o.1 ∧
        (∀ i, i < 2 * o.1 * 2 ^ o.2.2 → g.1 i ≤ rowBound o.1 (2 ^ o.2.2) S.inA S.inB i) ∧
        g.2 = 1 then
      some ((fun _ => S.outB, ((2 ^ S.w : ℕ) : ZMod S.q)) : (ℕ → ℕ) × ZMod S.q) else none)
      = some g' := hx
  split_ifs at hx' with hc
  cases hx'
  obtain ⟨hk, hlog, hk0, hB, hκ⟩ := hc
  obtain ⟨k', psi, logN⟩ := o
  simp only at hk hlog hk0 hB
  subst hk
  rw [hκ] at hW
  have hW' : LanesRep S.q S.w 1 (rowBound k' (2 ^ logN) S.inA S.inB)
      (rowCoeffs k' logN (fun j => sliceRow a (j * 2 ^ logN) (2 ^ logN))
        (fun j => sliceRow a (k' * 2 ^ logN + j * 2 ^ logN) (2 ^ logN))) W := by
    rw [rowCoeffs_slices]
    exact hW.mono hB
  exact accProgW_rel S k' hS psi logN hlog hk0 _ _ W hW'

end CatCrypt.Crypto.SecureCompilation.VIR.SignedLanes
