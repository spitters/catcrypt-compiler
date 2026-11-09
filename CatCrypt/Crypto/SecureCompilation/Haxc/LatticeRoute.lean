/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.BackHalf
public import CatCrypt.Crypto.SecureCompilation.Haxc.NttRouteSel
public import CatCrypt.Crypto.SecureCompilation.VIR.PointwiseAcc
public import CatCrypt.Crypto.SecureCompilation.VIR.RoundCodec

@[expose] public section

set_option autoImplicit false

/-!
# The lattice routes: base multiplication, accumulation and rounding codecs

The word programs of ML-KEM and ML-DSA polynomial arithmetic (`BasemulWord`,
`PointwiseAcc`) and rounding (`RoundCodec`) as route programs of the lane chain
`FieldChain.lanesChain`: the value numbering `gvnMR pure`, the lane lowering `lanesCom` and
the route wrapper. Each route theorem is the chain certificate (`lanesChain_denote`)
composed with the word theorem of the program.

A word program with `N` outputs on `M ≥ N` input lanes of `w`-bit words is run on `M`
lanes of 64-bit words by `latticeProg`: the casts of `NttRouteSel.widenProg` around
`padLanes`, which returns the `N` lanes followed by `M − N` zero lanes. A coefficient
program on one or two words is mapped over lanes by `coeffLane`, `coeffLane2` and, for
two results, `coeffLaneSplit`, which places the second results in the upper half.

## Main results

* `stackGet_latticeRoute`, `stackGet_latticeRoute_prog`: the output words of a route
  program of the lane chain, from its certificate.
* `basemulRoute_denote`, `pointwiseRoute_denote`, `accRoute_denote`: the base
  multiplication, the pointwise product and the row accumulation routes, from
  `basemulProgW_denote`, `pointwiseProgW_denote` and `accProgW_denote`.
* `compressRoute_denote`, `decompressRoute_denote`, `power2RoundRoute_denote`,
  `decomposeRoute_denote`, `makeHintRoute_denote`, `useHintRoute_denote`: the rounding
  codec routes, from the word theorems of `RoundCodec`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.LatticeRoute

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord
open CatCrypt.Crypto.SecureCompilation.VIR.PointwiseAcc
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (Rn)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Haxc (RouteProg)
open CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute (lanesCtx arrLimbs_eq_lanesVal)
open CatCrypt.Crypto.SecureCompilation.Haxc.NttRouteSel (widenProg hvGetG_widenProg)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain (lanesChain lanesChain_denote)
open Finset (range)

/-! ## 1. Lane programs with fewer outputs than inputs -/

section Pad

variable (w M N : ℕ)

/-- The lane of `M` lanes of `w`-bit words that is the constant `0`. -/
def zeroLane : Com jasminDialect (Ctxs w M) (Rw w) := .var (constE w 0) (.ret .here)

/-- The lane schedules `f 0, …, f (N − 1)` on `M` lanes, followed by `M − N` zero lanes:
    a program from `M` lanes to `M` lanes. -/
def padLanes (f : ℕ → Com jasminDialect (Ctxs w M) (Rw w)) :
    MultiReturnCom jasminDialect (Ctxs w M) (Ctxs w M) :=
  laneMapW M (fun i => if i < N then f i else zeroLane w M)

/-- Lane `i < N` of `padLanes` is lane `i` of `laneMapW N f`. -/
theorem hvGetG_padLanes (hNM : N ≤ M) (f : ℕ → Com jasminDialect (Ctxs w M) (Rw w))
    (V : Valuation (Ctxs w M)) (i : ℕ) (hi : i < N) :
    hvGetG (Rw w) (0 : BitVec w) ((padLanes w M N f).denote V) i
      = hvGetG (Rw w) (0 : BitVec w) ((laneMapW N f).denote V) i := by
  rw [padLanes, laneMapW_denote, laneMapW_denote, hvGetG_denoteN _ _ M _ _ i (by omega),
    hvGetG_denoteN _ _ _ _ _ _ hi, ite_eq_left hi]

/-- **A lane program of `w`-bit words from `M` lanes to `N ≤ M` lanes, on `M` lanes of
    64-bit words**: `padLanes` between the casts of `widenProg`. -/
def latticeProg (f : ℕ → Com jasminDialect (Ctxs w M) (Rw w)) :
    MultiReturnCom jasminDialect (Rn M) (Rn M) :=
  widenProg w M (padLanes w M N f)

/-- Lane `i < N` of `latticeProg` is lane `i` of `laneMapW N f` at the input words cast to
    `w` bits, cast to 64 bits. -/
theorem hvGetG_latticeProg (hNM : N ≤ M) (f : ℕ → Com jasminDialect (Ctxs w M) (Rw w))
    (g : ℕ → BitVec 64) (i : ℕ) (hi : i < N) :
    hvGetG R64 (0 : BitVec 64) ((latticeProg w M N f).denote (lanesVal R64 g M 0)) i
      = (hvGetG (Rw w) (0 : BitVec w) ((laneMapW N f).denote
          (lanesVal (Rw w) (fun j => (g j).setWidth w) M 0)) i).setWidth 64 := by
  rw [latticeProg, hvGetG_widenProg w M _ g i (by omega), hvGetG_padLanes w M N hNM f _ i hi]

end Pad

/-! ## 2. The route program of a lane program -/

section Route

variable (M : ℕ) (pure : jasminDialect.Op → Bool)

/-- **The route program of a lane program on `M` 64-bit lanes**: the run of the lane chain
    `lanesChain` (the value numbering `gvnMR pure`, the lane lowering and the route
    wrapper). -/
def latticeRoute (m : MultiReturnCom jasminDialect (Rn M) (Rn M)) :
    RouteProg (lanesCtx M) (arrTy M) :=
  ((lanesChain M pure).run m).get rfl

/-- The lane chain runs on a lane program to its route program. -/
theorem lanesChain_run_lattice (m : MultiReturnCom jasminDialect (Rn M) (Rn M)) :
    (lanesChain M pure).run m = some (latticeRoute M pure m) :=
  (Option.some_get _).symm

/-- **Word `i` of the output array of a route program**, from the certificate of the lane
    chain: lane `i` of the lane program at the input words. -/
theorem stackGet_latticeRoute (hM : M < 2 ^ 64) (m : MultiReturnCom jasminDialect (Rn M) (Rn M))
    (a o : Fin M → BitVec 64) (i : ℕ) (hi : i < M) :
    stackGet ((latticeRoute M pure m).denote (.cons a (.cons o .nil))) i
      = hvGetG R64 (0 : BitVec 64) (m.denote (lanesVal R64 (fun j => stackGet a j) M 0)) i := by
  have h := lanesChain_denote hM pure (lanesChain_run_lattice M pure m) a o
  rw [← arrLimbs_eq_lanesVal, ← h, arrLimbs_eq_lanesVal, hvGetG_lanesVal _ _ _ _ _ _ hi,
    Nat.zero_add]

/-- **Word `i < N` of the output array of the route program of `latticeProg`**: lane `i` of
    `laneMapW N f` at the low `w` bits of the input words. -/
theorem stackGet_latticeRoute_prog (w N : ℕ) (hM : M < 2 ^ 64) (hNM : N ≤ M) (hw : w ≤ 64)
    (f : ℕ → Com jasminDialect (Ctxs w M) (Rw w)) (a o : Fin M → BitVec 64) (i : ℕ)
    (hi : i < N) :
    (stackGet ((latticeRoute M pure (latticeProg w M N f)).denote (.cons a (.cons o .nil))) i
        ).setWidth w
      = hvGetG (Rw w) (0 : BitVec w) ((laneMapW N f).denote
          (lanesVal (Rw w) (fun j => (stackGet a j).setWidth w) M 0)) i := by
  rw [stackGet_latticeRoute M pure hM _ a o i (by omega), hvGetG_latticeProg w M N hNM f _ i hi,
    BitVec.setWidth_setWidth_of_le _ hw, BitVec.setWidth_eq]

end Route

/-! ## 3. Base multiplication, pointwise product and row accumulation -/

section Basemul

variable (pure : jasminDialect.Op → Bool)

/-- **The base multiplication route** on `2 · 2 ^ logN` words: the route program of
    `basemulProgW S psi logN` padded to `2 · 2 ^ logN` lanes. -/
def basemulRoute (S : BasemulSched) (psi logN : ℕ) :
    RouteProg (lanesCtx (2 * 2 ^ logN)) (arrTy (2 * 2 ^ logN)) :=
  latticeRoute (2 * 2 ^ logN) pure
    (latticeProg S.w (2 * 2 ^ logN) (2 ^ logN) (bmLane S psi (logN - 1) (2 ^ logN) (2 * 2 ^ logN)))

/-- **The output words of the base multiplication route.** On input words whose low `w`
    bits are at most `inB` in absolute value, the low `w` bits of output word `i < 2 ^ logN`
    are at most `outB` in absolute value and, times `2 ^ w`, are `blockMul 2` at the block
    roots of `ψ` of the two operands modulo `q`; from `basemulProgW_denote`. -/
theorem basemulRoute_denote (S : BasemulSched) (hS : S.Ok) (hw : S.w ≤ 64) (psi logN : ℕ)
    (hlog : 0 < logN) (hM : 2 * 2 ^ logN < 2 ^ 64) (a o : Fin (2 * 2 ^ logN) → BitVec 64)
    (ha : ∀ j, j < 2 * 2 ^ logN → |((stackGet a j).setWidth S.w).toInt| ≤ S.inB)
    (i : ℕ) (hi : i < 2 ^ logN) :
    |((stackGet ((basemulRoute pure S psi logN).denote (.cons a (.cons o .nil))) i).setWidth
        S.w).toInt| ≤ S.outB ∧
    ((((stackGet ((basemulRoute pure S psi logN).denote (.cons a (.cons o .nil))) i).setWidth
        S.w).toInt : ℤ) : ZMod S.q) * ((2 ^ S.w : ℕ) : ZMod S.q)
      = blockMul 2 (blockRoot (psi : ZMod S.q) (logN - 1))
          (fun j => (((stackGet a j).setWidth S.w).toInt : ZMod S.q))
          (fun j => (((stackGet a (2 ^ logN + j)).setWidth S.w).toInt : ZMod S.q)) i := by
  rw [basemulRoute, stackGet_latticeRoute_prog _ pure _ _ hM (by omega) hw _ a o i hi]
  exact basemulProgW_denote S hS psi logN hlog _ ha i hi

/-- **The pointwise product route** on `2 · 2 ^ logN` words: the route program of
    `pointwiseProgW S logN` padded to `2 · 2 ^ logN` lanes. -/
def pointwiseRoute (S : BasemulSched) (logN : ℕ) :
    RouteProg (lanesCtx (2 * 2 ^ logN)) (arrTy (2 * 2 ^ logN)) :=
  latticeRoute (2 * 2 ^ logN) pure
    (latticeProg S.w (2 * 2 ^ logN) (2 ^ logN) (pwLane S (2 ^ logN) (2 * 2 ^ logN)))

/-- **The output words of the pointwise product route.** On input words whose low `w`
    bits are at most `inB` in absolute value, the low `w` bits of output word `i < 2 ^ logN`
    are at most `outB` in absolute value and, times `2 ^ w`, are the product of the two
    operands modulo `q`; from `pointwiseProgW_denote`. -/
theorem pointwiseRoute_denote (S : BasemulSched) (hS : S.PointwiseOk) (hw : S.w ≤ 64)
    (logN : ℕ) (hM : 2 * 2 ^ logN < 2 ^ 64) (a o : Fin (2 * 2 ^ logN) → BitVec 64)
    (ha : ∀ j, j < 2 * 2 ^ logN → |((stackGet a j).setWidth S.w).toInt| ≤ S.inB)
    (i : ℕ) (hi : i < 2 ^ logN) :
    |((stackGet ((pointwiseRoute pure S logN).denote (.cons a (.cons o .nil))) i).setWidth
        S.w).toInt| ≤ S.outB ∧
    ((((stackGet ((pointwiseRoute pure S logN).denote (.cons a (.cons o .nil))) i).setWidth
        S.w).toInt : ℤ) : ZMod S.q) * ((2 ^ S.w : ℕ) : ZMod S.q)
      = (((stackGet a i).setWidth S.w).toInt : ZMod S.q)
          * (((stackGet a (2 ^ logN + i)).setWidth S.w).toInt : ZMod S.q) := by
  rw [pointwiseRoute, stackGet_latticeRoute_prog _ pure _ _ hM (by omega) hw _ a o i hi]
  exact pointwiseProgW_denote S hS logN _ ha i hi

/-- **The row accumulation route** on `2 · k · 2 ^ logN` words: the route program of
    `accProgW S k psi logN` padded to `2 · k · 2 ^ logN` lanes. -/
def accRoute (S : AccSched) (k psi logN : ℕ) :
    RouteProg (lanesCtx (2 * k * 2 ^ logN)) (arrTy (2 * k * 2 ^ logN)) :=
  latticeRoute (2 * k * 2 ^ logN) pure
    (latticeProg S.w (2 * k * 2 ^ logN) (2 ^ logN)
      (accLane S k psi (logN - 1) (2 ^ logN) (2 * k * 2 ^ logN)))

/-- **The output words of the row accumulation route.** On first-operand words whose low
    `w` bits are at most `inA` and second-operand words whose low `w` bits are at most `inB`
    in absolute value, the low `w` bits of output word `i < 2 ^ logN` are at most `outB` in
    absolute value and, times `2 ^ w`, are the sum over the row of `blockMul 2` at the
    block roots of `ψ` modulo `q`; from `accProgW_denote`. -/
theorem accRoute_denote (S : AccSched) (k : ℕ) (hS : S.Ok k) (hw : S.w ≤ 64) (psi logN : ℕ)
    (hlog : 0 < logN) (hk : 0 < k) (hM : 2 * k * 2 ^ logN < 2 ^ 64)
    (a o : Fin (2 * k * 2 ^ logN) → BitVec 64)
    (hA : ∀ j t, j < k → t < 2 ^ logN →
      |((stackGet a (j * 2 ^ logN + t)).setWidth S.w).toInt| ≤ S.inA)
    (hB : ∀ j t, j < k → t < 2 ^ logN →
      |((stackGet a (k * 2 ^ logN + j * 2 ^ logN + t)).setWidth S.w).toInt| ≤ S.inB)
    (i : ℕ) (hi : i < 2 ^ logN) :
    |((stackGet ((accRoute pure S k psi logN).denote (.cons a (.cons o .nil))) i).setWidth
        S.w).toInt| ≤ S.outB ∧
    ((((stackGet ((accRoute pure S k psi logN).denote (.cons a (.cons o .nil))) i).setWidth
        S.w).toInt : ℤ) : ZMod S.q) * ((2 ^ S.w : ℕ) : ZMod S.q)
      = ∑ j ∈ range k, blockMul 2 (blockRoot (psi : ZMod S.q) (logN - 1))
          (fun t => (((stackGet a (j * 2 ^ logN + t)).setWidth S.w).toInt : ZMod S.q))
          (fun t => (((stackGet a (k * 2 ^ logN + j * 2 ^ logN + t)).setWidth S.w).toInt
            : ZMod S.q)) i := by
  have hkN : 2 ^ logN ≤ 2 * k * 2 ^ logN :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [accRoute, stackGet_latticeRoute_prog _ pure _ _ hM hkN hw _ a o i hi]
  exact accProgW_denote S k hS psi logN hlog hk (fun j => (stackGet a j).setWidth S.w) hA hB i hi

end Basemul

/-! ## 4. Coefficient programs on lanes -/

section Coeff

/-- The program returning all results of `m` but the first. -/
def mrTail {d : Dialect} [DialectSignature d] :
    {Γ : Ctxt d} → {t : d.Ty} → {ts : List d.Ty} →
    MultiReturnCom d Γ (t :: ts) → MultiReturnCom d Γ ts
  | _, _, _, .ret (.cons _ vs) => .ret vs
  | _, _, _, .var e body => .var e (mrTail body)

/-- `mrTail` denotes the tail of the multi-return denotation. -/
theorem mrTail_denote {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d] :
    ∀ {Γ : Ctxt d} {t : d.Ty} {ts : List d.Ty}
      (m : MultiReturnCom d Γ (t :: ts)) (V : Valuation Γ),
      (mrTail m).denote V = (m.denote V).tail
  | _, _, _, .ret (.cons _ _), _ => by
      simp [mrTail, MultiReturnCom.denote, MultiReturnCom.lookupVars, HVector.tail]
  | _, _, _, .var _ body, V => by
      simp [mrTail, MultiReturnCom.denote, mrTail_denote body]

variable (w : ℕ)

/-- **A one-input coefficient program on lanes**: lane `i` of `n` lanes is the first
    result of `m` at lane `i`. -/
def coeffLane (m : MultiReturnCom jasminDialect [Rw w] (Rw w :: [])) :
    (n : ℕ) → ℕ → Com jasminDialect (Ctxs w n) (Rw w)
  | 0, _ => .var (constE w 0) (.ret .here)
  | n + 1, i => (MultiReturnCom.rename (hvToHom (.cons (laneVarG (Rw w) n i) .nil)) m).toComHead

theorem coeffLane_denote (m : MultiReturnCom jasminDialect [Rw w] (Rw w :: [])) (N : ℕ)
    (g : ℕ → BitVec w) (i : ℕ) (hi : i < N) :
    (coeffLane w m N i).denote (lanesVal (Rw w) g N 0) = (m.denote (.cons (g i) .nil)).head := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [coeffLane, MultiReturnCom.toComHead_denote, multiReturnCom_denote_rename, pullV_hvToHom]
  show (m.denote (.cons ((laneVarG (Rw w) n i).lookup (lanesVal (Rw w) g (n + 1) 0)) .nil)).head
    = _
  rw [laneVarG_lookup (Rw w) g n i 0 (by omega), Nat.zero_add]

/-- **A two-input coefficient program on lanes**: lane `i` of `n` lanes is the result of
    `m` at lanes `i` and `K + i`. -/
def coeffLane2 (K : ℕ) (m : MultiReturnCom jasminDialect [Rw w, Rw w] (Rw w :: [])) :
    (n : ℕ) → ℕ → Com jasminDialect (Ctxs w n) (Rw w)
  | 0, _ => .var (constE w 0) (.ret .here)
  | n + 1, i => (MultiReturnCom.rename
      (hvToHom (.cons (laneVarG (Rw w) n i) (.cons (laneVarG (Rw w) n (K + i)) .nil))) m).toComHead

theorem coeffLane2_denote (K : ℕ) (m : MultiReturnCom jasminDialect [Rw w, Rw w] (Rw w :: []))
    (M : ℕ) (g : ℕ → BitVec w) (i : ℕ) (hi : K + i < M) :
    (coeffLane2 w K m M i).denote (lanesVal (Rw w) g M 0)
      = (m.denote (.cons (g i) (.cons (g (K + i)) .nil))).head := by
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  rw [coeffLane2, MultiReturnCom.toComHead_denote, multiReturnCom_denote_rename, pullV_hvToHom]
  show (m.denote (.cons ((laneVarG (Rw w) n i).lookup (lanesVal (Rw w) g (n + 1) 0))
    (.cons ((laneVarG (Rw w) n (K + i)).lookup (lanesVal (Rw w) g (n + 1) 0)) .nil))).head = _
  rw [laneVarG_lookup (Rw w) g n i 0 (by omega), laneVarG_lookup (Rw w) g n (K + i) 0 (by omega),
    Nat.zero_add, Nat.zero_add]

/-- **A two-output coefficient program on lanes**: lane `i < K` of `n` lanes is the first
    result of `m` at lane `i`, and lane `i ≥ K` its second result at lane `i - K`. -/
def coeffLaneSplit (K : ℕ) (m : MultiReturnCom jasminDialect [Rw w] [Rw w, Rw w]) :
    (n : ℕ) → ℕ → Com jasminDialect (Ctxs w n) (Rw w)
  | 0, _ => .var (constE w 0) (.ret .here)
  | n + 1, i =>
    if i < K then
      (MultiReturnCom.rename (hvToHom (.cons (laneVarG (Rw w) n i) .nil)) m).toComHead
    else
      (mrTail (MultiReturnCom.rename (hvToHom (.cons (laneVarG (Rw w) n (i - K)) .nil)) m)
        ).toComHead

theorem coeffLaneSplit_denote_lo (K : ℕ) (m : MultiReturnCom jasminDialect [Rw w] [Rw w, Rw w])
    (M : ℕ) (g : ℕ → BitVec w) (i : ℕ) (hi : i < K) (hKM : K ≤ M) :
    (coeffLaneSplit w K m M i).denote (lanesVal (Rw w) g M 0)
      = (m.denote (.cons (g i) .nil)).head := by
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  rw [coeffLaneSplit, ite_eq_left hi, MultiReturnCom.toComHead_denote, multiReturnCom_denote_rename,
    pullV_hvToHom]
  show (m.denote (.cons ((laneVarG (Rw w) n i).lookup (lanesVal (Rw w) g (n + 1) 0)) .nil)).head
    = _
  rw [laneVarG_lookup (Rw w) g n i 0 (by omega), Nat.zero_add]

theorem coeffLaneSplit_denote_hi (K : ℕ) (m : MultiReturnCom jasminDialect [Rw w] [Rw w, Rw w])
    (M : ℕ) (g : ℕ → BitVec w) (i : ℕ) (hi : i < M) (hKi : K ≤ i) :
    (coeffLaneSplit w K m M i).denote (lanesVal (Rw w) g M 0)
      = (m.denote (.cons (g (i - K)) .nil)).tail.head := by
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  rw [coeffLaneSplit, ite_eq_right (by omega), MultiReturnCom.toComHead_denote, mrTail_denote,
    multiReturnCom_denote_rename, pullV_hvToHom]
  show (m.denote (.cons ((laneVarG (Rw w) n (i - K)).lookup (lanesVal (Rw w) g (n + 1) 0))
    .nil)).tail.head = _
  rw [laneVarG_lookup (Rw w) g n (i - K) 0 (by omega), Nat.zero_add]

/-- The reading of the first entry of a valuation is the first reading. -/
theorem zvals_head (s : Bool) {t : JasminTy} {ts : List JasminTy} :
    ∀ X : HVector (fun t => ⟦t⟧) (t :: ts),
      (ComRangeExact.zvals s X).head = ComRangeExact.rdT s t X.head
  | .cons _ _ => rfl

/-- The readings of the tail of a valuation are the tail of the readings. -/
theorem zvals_tail (s : Bool) {t : JasminTy} {ts : List JasminTy} :
    ∀ X : HVector (fun t => ⟦t⟧) (t :: ts),
      (ComRangeExact.zvals s X).tail = ComRangeExact.zvals s X.tail
  | .cons _ _ => rfl

end Coeff

/-! ## 5. The rounding codec routes -/

section Codec

open CatCrypt.Crypto.SecureCompilation.VIR.RoundCodec
open CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact (rd boundsOkMR zvals)
open CatCrypt.Crypto.SecureCompilation.RangeDomain (Iv)

variable (pure : jasminDialect.Op → Bool) (N : ℕ)

/-- **The ML-KEM compression route** on `N` words: `compressProg d P` on every lane. -/
def compressRoute (d : ℕ) (P : CompressMagic) : RouteProg (lanesCtx N) (arrTy N) :=
  latticeRoute N pure (latticeProg P.w N N (coeffLane P.w (compressProg d P) N))

/-- **The output words of the compression route.** Under `CompressOk` and the bounds check
    of `compressProg`, on input words whose low `w` bits are below `q`, the unsigned value
    of the low `w` bits of output word `i` is `Compress_d` of input word `i`; from
    `compress_denote`. -/
theorem compressRoute_denote (q d : ℕ) (P : CompressMagic) (h : CompressOk q d P = true)
    (hb : boundsOkMR false (iv1 (0, (q : ℤ) - 1)) (compressProg d P)
      (iv1 (0, 2 ^ d - 1)) = true) (hw : P.w ≤ 64) (hM : N < 2 ^ 64)
    (a o : Fin N → BitVec 64) (ha : ∀ j, j < N → ((stackGet a j).setWidth P.w).toNat < q)
    (i : ℕ) (hi : i < N) :
    rd false ((stackGet ((compressRoute pure N d P).denote (.cons a (.cons o .nil))) i).setWidth
        P.w)
      = compressSpec q d ((stackGet a i).setWidth P.w).toNat := by
  rw [compressRoute, stackGet_latticeRoute_prog _ pure _ _ hM le_rfl hw _ a o i hi,
    laneMapW_denote, hvGetG_denoteN _ _ _ _ _ _ hi, coeffLane_denote _ _ _ _ i hi]
  have e := congrArg HVector.head (compress_denote q d P h hb _ (ha i hi))
  rw [zvals_head] at e
  exact e

/-- **The ML-KEM decompression route** on `N` words: `decompressProg w q d` on every
    lane. -/
def decompressRoute (w q d : ℕ) : RouteProg (lanesCtx N) (arrTy N) :=
  latticeRoute N pure (latticeProg w N N (coeffLane w (decompressProg w q d) N))

/-- **The output words of the decompression route.** Under the bounds check of
    `decompressProg`, on input words whose low `w` bits are below `2 ^ d`, the unsigned
    value of the low `w` bits of output word `i` is `Decompress_d` of input word `i`; from
    `decompress_denote`. -/
theorem decompressRoute_denote (w q d : ℕ) (hq : q < 2 ^ w) (hd : 2 ^ d / 2 < 2 ^ w)
    (hb : boundsOkMR false (iv1 (0, 2 ^ d - 1)) (decompressProg w q d)
      (iv1 (0, (q : ℤ) - 1)) = true) (hw : w ≤ 64) (hM : N < 2 ^ 64)
    (a o : Fin N → BitVec 64) (ha : ∀ j, j < N → ((stackGet a j).setWidth w).toNat < 2 ^ d)
    (i : ℕ) (hi : i < N) :
    rd false ((stackGet ((decompressRoute pure N w q d).denote (.cons a (.cons o .nil))) i
        ).setWidth w)
      = decompressSpec q d ((stackGet a i).setWidth w).toNat := by
  rw [decompressRoute, stackGet_latticeRoute_prog _ pure _ _ hM le_rfl hw _ a o i hi,
    laneMapW_denote, hvGetG_denoteN _ _ _ _ _ _ hi, coeffLane_denote _ _ _ _ i hi]
  have e := congrArg HVector.head (decompress_denote w q d hq hd hb _ (ha i hi))
  rw [zvals_head] at e
  exact e

/-- **The ML-DSA `Power2Round` route** on `2 N` words: `power2RoundProg 32 13` on the
    first `N` lanes, its first results in lanes `0, …, N − 1` and its second results in
    lanes `N, …, 2 N − 1`. -/
def power2RoundRoute : RouteProg (lanesCtx (2 * N)) (arrTy (2 * N)) :=
  latticeRoute (2 * N) pure
    (latticeProg 32 (2 * N) (2 * N) (coeffLaneSplit 32 N (power2RoundProg 32 13) (2 * N)))

/-- **The output words of the `Power2Round` route.** Under the bounds check of
    `power2RoundProg`, on input words whose low 32 bits read as a signed integer in
    `[0, q)`, the signed values of the low 32 bits of output words `i` and `N + i` are the
    two parts of FIPS 204 `Power2Round` of input word `i`; from `power2Round_denote`. -/
theorem power2RoundRoute_denote (outs : HVector (fun _ => Iv) (C2 32))
    (hb : boundsOkMR true (iv1 (0, Fips204.q - 1)) (power2RoundProg 32 13) outs = true)
    (hM : 2 * N < 2 ^ 64) (a o : Fin (2 * N) → BitVec 64)
    (ha : ∀ j, j < N → 0 ≤ rd true ((stackGet a j).setWidth 32)
      ∧ rd true ((stackGet a j).setWidth 32) < Fips204.q)
    (i : ℕ) (hi : i < N) :
    rd true ((stackGet ((power2RoundRoute pure N).denote (.cons a (.cons o .nil))) i).setWidth
        32) = (Fips204.power2Round (rd true ((stackGet a i).setWidth 32))).1 ∧
    rd true ((stackGet ((power2RoundRoute pure N).denote (.cons a (.cons o .nil))) (N + i)
        ).setWidth 32) = (Fips204.power2Round (rd true ((stackGet a i).setWidth 32))).2 := by
  have e := power2Round_denote outs hb _ (ha i hi).1 (ha i hi).2
  have hi2 : i < 2 * N := by omega
  have hNi : N + i < 2 * N := by omega
  have hN2 : N ≤ 2 * N := by omega
  constructor
  · rw [power2RoundRoute, stackGet_latticeRoute_prog (2 * N) pure 32 (2 * N) hM le_rfl
      (by norm_num) _ a o i hi2, laneMapW_denote, hvGetG_denoteN _ _ (2 * N) _ _ i hi2,
      coeffLaneSplit_denote_lo 32 N _ (2 * N) _ i hi hN2]
    have e1 := congrArg HVector.head e
    rw [zvals_head] at e1
    exact e1
  · rw [power2RoundRoute, stackGet_latticeRoute_prog (2 * N) pure 32 (2 * N) hM le_rfl
      (by norm_num) _ a o (N + i) hNi, laneMapW_denote, hvGetG_denoteN _ _ (2 * N) _ _ (N + i) hNi,
      coeffLaneSplit_denote_hi 32 N _ (2 * N) _ (N + i) hNi (Nat.le_add_right N i),
      Nat.add_sub_cancel_left]
    have e2 := congrArg (fun X => HVector.head (HVector.tail X)) e
    rw [zvals_tail, zvals_head] at e2
    exact e2

/-- **The ML-DSA `Decompose` route** on `2 N` words: `decomposeProg P` on the first `N`
    lanes, `HighBits` in lanes `0, …, N − 1` and `LowBits` in lanes `N, …, 2 N − 1`. -/
def decomposeRoute (P : DecomposeMagic) : RouteProg (lanesCtx (2 * N)) (arrTy (2 * N)) :=
  latticeRoute (2 * N) pure
    (latticeProg P.w (2 * N) (2 * N) (coeffLaneSplit P.w N (decomposeProg P) (2 * N)))

/-- **The output words of the `Decompose` route**, at both ML-DSA instances. Under the
    bounds check of `decomposeProg`, on input words whose low `w` bits read as a signed
    integer in `[0, q)`, the signed values of the low `w` bits of output words `i` and
    `N + i` are `HighBits` and `LowBits` of input word `i`; from `decompose_denote`. -/
theorem decomposeRoute_denote {P : DecomposeMagic} {γ2 : ℤ} (hP : MldsaInst P γ2)
    (outs : HVector (fun _ => Iv) (C2 P.w))
    (hb : boundsOkMR true (iv1 (0, Fips204.q - 1)) (decomposeProg P) outs = true)
    (hw : P.w ≤ 64) (hM : 2 * N < 2 ^ 64) (a o : Fin (2 * N) → BitVec 64)
    (ha : ∀ j, j < N → 0 ≤ rd true ((stackGet a j).setWidth P.w)
      ∧ rd true ((stackGet a j).setWidth P.w) < Fips204.q)
    (i : ℕ) (hi : i < N) :
    rd true ((stackGet ((decomposeRoute pure N P).denote (.cons a (.cons o .nil))) i).setWidth
        P.w) = Fips204.highBits γ2 (rd true ((stackGet a i).setWidth P.w)) ∧
    rd true ((stackGet ((decomposeRoute pure N P).denote (.cons a (.cons o .nil))) (N + i)
        ).setWidth P.w) = Fips204.lowBits γ2 (rd true ((stackGet a i).setWidth P.w)) := by
  have e := decompose_denote hP outs hb _ (ha i hi).1 (ha i hi).2
  have hi2 : i < 2 * N := by omega
  have hNi : N + i < 2 * N := by omega
  have hN2 : N ≤ 2 * N := by omega
  constructor
  · rw [decomposeRoute, stackGet_latticeRoute_prog (2 * N) pure P.w (2 * N) hM le_rfl hw _ a o
      i hi2, laneMapW_denote, hvGetG_denoteN _ _ (2 * N) _ _ i hi2,
      coeffLaneSplit_denote_lo P.w N _ (2 * N) _ i hi hN2]
    have e1 := congrArg HVector.head e
    rw [zvals_head] at e1
    exact e1
  · rw [decomposeRoute, stackGet_latticeRoute_prog (2 * N) pure P.w (2 * N) hM le_rfl hw _ a o
      (N + i) hNi, laneMapW_denote, hvGetG_denoteN _ _ (2 * N) _ _ (N + i) hNi,
      coeffLaneSplit_denote_hi P.w N _ (2 * N) _ (N + i) hNi (Nat.le_add_right N i),
      Nat.add_sub_cancel_left]
    have e2 := congrArg (fun X => HVector.head (HVector.tail X)) e
    rw [zvals_tail, zvals_head] at e2
    exact e2

/-- **The ML-DSA `MakeHint` route** on `2 N` words: `makeHintProg P` on lanes `i` (`r`) and
    `N + i` (`z`), its result in lane `i`, padded to `2 N` lanes. -/
def makeHintRoute (P : DecomposeMagic) : RouteProg (lanesCtx (2 * N)) (arrTy (2 * N)) :=
  latticeRoute (2 * N) pure
    (latticeProg P.w (2 * N) N (coeffLane2 P.w N (makeHintProg P) (2 * N)))

/-- **The output words of the `MakeHint` route**, at both ML-DSA instances. Under the
    bounds check of `makeHintProg`, on `r` words in `[0, q)` and `z` words in `[-γ₂, γ₂]`
    (signed readings of the low `w` bits), the signed value of the low `w` bits of output
    word `i < N` is `1` when `MakeHint (z, r)` holds and `0` otherwise; from
    `makeHint_denote`. -/
theorem makeHintRoute_denote {P : DecomposeMagic} {γ2 : ℤ} (hP : MldsaInst P γ2)
    (out : HVector (fun _ => Iv) (C1 P.w))
    (hb : boundsOkMR true (iv2 (0, Fips204.q - 1) (-γ2, γ2)) (makeHintProg P) out = true)
    (hw : P.w ≤ 64) (hM : 2 * N < 2 ^ 64) (a o : Fin (2 * N) → BitVec 64) (i : ℕ) (hi : i < N)
    (h0 : 0 ≤ rd true ((stackGet a i).setWidth P.w))
    (h1 : rd true ((stackGet a i).setWidth P.w) < Fips204.q)
    (hz0 : -γ2 ≤ rd true ((stackGet a (N + i)).setWidth P.w))
    (hz1 : rd true ((stackGet a (N + i)).setWidth P.w) ≤ γ2) :
    rd true ((stackGet ((makeHintRoute pure N P).denote (.cons a (.cons o .nil))) i).setWidth
        P.w)
      = if Fips204.makeHint γ2 (rd true ((stackGet a (N + i)).setWidth P.w))
          (rd true ((stackGet a i).setWidth P.w)) then 1 else 0 := by
  rw [makeHintRoute, stackGet_latticeRoute_prog _ pure _ _ hM (by omega) hw _ a o i hi,
    laneMapW_denote, hvGetG_denoteN _ _ _ _ _ _ hi,
    coeffLane2_denote P.w N _ (2 * N) _ i (show N + i < 2 * N by omega)]
  have e := congrArg HVector.head (makeHint_denote hP out hb _ _ h0 h1 hz0 hz1)
  rw [zvals_head] at e
  exact e

/-- **The ML-DSA `UseHint` route** on `2 N` words: `useHintProg P` on lanes `i` (`r`) and
    `N + i` (`h`), its result in lane `i`, padded to `2 N` lanes. -/
def useHintRoute (P : DecomposeMagic) : RouteProg (lanesCtx (2 * N)) (arrTy (2 * N)) :=
  latticeRoute (2 * N) pure
    (latticeProg P.w (2 * N) N (coeffLane2 P.w N (useHintProg P) (2 * N)))

/-- **The output words of the `UseHint` route**, at both ML-DSA instances. Under the bounds
    check of `useHintProg`, on `r` words in `[0, q)` and hint words in `[0, 1]` (signed
    readings of the low `w` bits), the signed value of the low `w` bits of output word
    `i < N` is FIPS 204 `UseHint`; from `useHint_denote`. -/
theorem useHintRoute_denote {P : DecomposeMagic} {γ2 : ℤ} (hP : MldsaInst P γ2)
    (out : HVector (fun _ => Iv) (C1 P.w))
    (hb : boundsOkMR true (iv2 (0, Fips204.q - 1) (0, 1)) (useHintProg P) out = true)
    (hw : P.w ≤ 64) (hM : 2 * N < 2 ^ 64) (a o : Fin (2 * N) → BitVec 64) (i : ℕ) (hi : i < N)
    (h0 : 0 ≤ rd true ((stackGet a i).setWidth P.w))
    (h1 : rd true ((stackGet a i).setWidth P.w) < Fips204.q)
    (hh0 : 0 ≤ rd true ((stackGet a (N + i)).setWidth P.w))
    (hh1 : rd true ((stackGet a (N + i)).setWidth P.w) ≤ 1) :
    rd true ((stackGet ((useHintRoute pure N P).denote (.cons a (.cons o .nil))) i).setWidth
        P.w)
      = Fips204.useHint γ2 (decide (rd true ((stackGet a (N + i)).setWidth P.w) = 1))
          (rd true ((stackGet a i).setWidth P.w)) := by
  rw [useHintRoute, stackGet_latticeRoute_prog _ pure _ _ hM (by omega) hw _ a o i hi,
    laneMapW_denote, hvGetG_denoteN _ _ _ _ _ _ hi,
    coeffLane2_denote P.w N _ (2 * N) _ i (show N + i < 2 * N by omega)]
  have e := congrArg HVector.head (useHint_denote hP out hb _ _ h0 h1 hh0 hh1)
  rw [zvals_head] at e
  exact e

end Codec

end CatCrypt.Crypto.SecureCompilation.Haxc.LatticeRoute
