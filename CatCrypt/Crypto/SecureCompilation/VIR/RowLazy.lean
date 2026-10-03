/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgRel
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.LanesRep

/-!
# The row product with an unreduced wide accumulator

The row product `∑_{j < k} a_j ∘ b_j` of one NTT block of length `2` (an ML-KEM pair) is a
counted loop with an unreduced accumulator and one reduction after the loop.

At ring level, `rowDialect` has a type `wide q` of unreduced pair accumulators beside the
type `pair q` of reduced pairs, an op `mulAcc ζ` that adds the base product of two pairs
into a wide accumulator, and an op `reduce` from `wide q` to `pair q`. Over `ZMod q` both
types denote `ZMod q × ZMod q` and `reduce` is the identity; the word level gives the two
types different representations, and the Montgomery factor `2 ^ w` sits in the relation of
the reduced pair.

At word level, `rowLoopW` is the same loop over `jasminDialect`: the rows are four stack
arrays of signed `w`-bit words, the carried tuple is three `2 w`-bit accumulators (the even
products, the twiddled odd products and the cross products), and after the loop one
reduction pass applies `smontAccW` to the twiddled sum, multiplies by the Montgomery
twiddle and reduces both outputs.

The two loops are related by `NFProg.denote_forLoop_rel_graded` at the grade
`Rc j = WideRep (j · inA · inB)`: after `j` trips every accumulator lies within `j` times
the product bound. The bound checks are the conjuncts of `AccSched.Ok k`.

## Main definitions

* `RowTy`, `RowOp`, `rowDialect`: the ring-level dialect with the wide type, `mulAcc` and
  `reduce`.
* `bm`: the base product of two pairs at the twiddle `ζ`.
* `rowBody`, `rowTail`, `rowLoop`: the ring-level row product as an `NFProg`.
* `sextN`, `prodN`, `macN`, `redN`, `loadE`: the word blocks of `BasemulWord` as `NFProg`
  prefixes, and the stack-array load.
* `rowBodyW`, `rowTailW`, `rowLoopW`: the word-level loop with `2 w`-bit accumulators and
  one final reduction pass.
* `WideRep`: the representation of a wide accumulator by three `2 w`-bit words at a bound.
* `RowIn`, `RowOut`: the relations of the inputs and of the outputs.

## Main results

* `rowLoop_denote`: the ring-level loop returns `∑_{j < n} bm ζ (a j) (b j)`.
* `rowLoop_basemulF`: at the rows of block `c` of polynomials in the NTT domain the two
  outputs are the sums of `basemulF` at lanes `2 c` and `2 c + 1`.
* `wideRep_step`: one multiply-accumulate trip raises the grade by `inA · inB`.
* `wideRep_final`: the final reduction pass sends a wide accumulator at grade `k · inA · inB`
  to two output words representing the reduced pair with factor `2 ^ w` within `outB`.
* `rowLoop_rel`: under `AccSched.Ok k` the two loops are `Option.Rel RowOut`-related.
* `mlkemRow3_rel`: the instance at ML-KEM `k = 3` from `mlkemAcc3_ok`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.RowLazy

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord
open CatCrypt.Crypto.SecureCompilation.VIR.PointwiseAcc
open CatCrypt.Crypto.SecureCompilation.VIR.SignedLanes (SRep)
open CatCrypt.Crypto.SecureCompilation.VIR.RingDialect (Limbs basemulF rowLanes)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open Finset (range)

/-! ## 1. The ring-level dialect -/

/-- The types of the row dialect: the trip counter, a bit, a row of pairs modulo `q`, a
reduced pair and an unreduced (wide) pair accumulator. -/
inductive RowTy where
  /-- The 64-bit trip counter. -/
  | word
  /-- A bit. -/
  | bit
  /-- A row of pairs modulo `q`, indexed by the trip index. -/
  | row (q : ℕ)
  /-- A reduced pair modulo `q`. -/
  | pair (q : ℕ)
  /-- An unreduced pair accumulator modulo `q`. -/
  | wide (q : ℕ)

/-- Over `ZMod q` a reduced pair and a wide accumulator both denote `ZMod q × ZMod q`. -/
@[reducible] instance : TyDenote RowTy where
  denote
    | .word => BitVec 64
    | .bit => Bool
    | .row q => ℕ → ZMod q × ZMod q
    | .pair q => ZMod q × ZMod q
    | .wide q => ZMod q × ZMod q

/-- The ops of the row dialect. -/
inductive RowOp where
  /-- Entry `i` of a row. -/
  | get (q : ℕ)
  /-- The zero wide accumulator. -/
  | zero (q : ℕ)
  /-- Add the base product of two pairs at the twiddle `ζ` into a wide accumulator. -/
  | mulAcc (q : ℕ) (ζ : ZMod q)
  /-- The reduction of a wide accumulator to a pair. -/
  | reduce (q : ℕ)

/-- The row dialect. -/
@[reducible] def rowDialect : Dialect := { Op := RowOp, Ty := RowTy }

instance : DialectSignature rowDialect where
  sig
    | .get q => [.row q, .word]
    | .zero _ => []
    | .mulAcc q _ => [.wide q, .pair q, .pair q]
    | .reduce q => [.wide q]
  ret
    | .get q => .pair q
    | .zero q => .wide q
    | .mulAcc q _ => .wide q
    | .reduce q => .pair q

/-- The base product of two pairs in `ZMod q [X] / (X ^ 2 − ζ)`. -/
def bm {q : ℕ} (ζ : ZMod q) (a b : ZMod q × ZMod q) : ZMod q × ZMod q :=
  (a.1 * b.1 + a.2 * b.2 * ζ, a.1 * b.2 + a.2 * b.1)

instance : DialectDenote rowDialect where
  denote
    | .get q => fun a =>
        (show ℕ → ZMod q × ZMod q from a.head) (show BitVec 64 from a.tail.head).toNat
    | .zero _ => fun _ => (0, 0)
    | .mulAcc q ζ => fun a =>
        (show ZMod q × ZMod q from a.head) +
          bm ζ (show ZMod q × ZMod q from a.tail.head)
            (show ZMod q × ZMod q from a.tail.tail.head)
    | .reduce q => fun a => (show ZMod q × ZMod q from a.head)

/-- The trip counter of `rowDialect` is its `word` type. -/
instance : HasWord64 rowDialect where
  word := RowTy.word
  toNat := BitVec.toNat
  ofNat := BitVec.ofNat 64

/-- The bit type of `rowDialect`. -/
instance : HasBitType rowDialect where
  bit := RowTy.bit

/-- The bit of `rowDialect` denotes a `Bool`. -/
instance : HasBoolBit rowDialect where
  toBool := id

/-! ## 2. The ring-level loop -/

/-- The context of the row product: the trip count and the two rows. -/
abbrev SrcCtx (q : ℕ) : Ctxt rowDialect := [RowTy.word, RowTy.row q, RowTy.row q]

/-- The loop body: read entry `i` of both rows and add their base product into the
accumulator. -/
def rowBody (q : ℕ) (ζ : ZMod q) :
    NFProg rowDialect
      [RowTy.wide q, RowTy.word, RowTy.wide q, RowTy.word, RowTy.row q, RowTy.row q]
      [RowTy.wide q] :=
  .var ⟨RowOp.get q, rfl,
    .cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil)⟩ <|
  .var ⟨RowOp.get q, rfl,
    .cons (.there (.there (.there (.there (.there (.there .here))))))
      (.cons (.there (.there .here)) .nil)⟩ <|
  .var ⟨RowOp.mulAcc q ζ, rfl,
    .cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))⟩ <|
  .ret (.cons .here .nil)

/-- After the loop: the reduction of the wide accumulator. -/
def rowTail (q : ℕ) : NFProg rowDialect
    [RowTy.wide q, RowTy.wide q, RowTy.word, RowTy.row q, RowTy.row q] [RowTy.pair q] :=
  .var ⟨RowOp.reduce q, rfl, .cons .here .nil⟩ (.ret (.cons .here .nil))

/-- **The ring-level row product.** From the zero wide accumulator, `n` trips of
`mulAcc ζ` on entry `i` of both rows, then one `reduce`. -/
def rowLoop (q : ℕ) (ζ : ZMod q) : NFProg rowDialect (SrcCtx q) [RowTy.pair q] :=
  .var (t := RowTy.wide q) ⟨RowOp.zero q, rfl, .nil⟩
    (NFProg.forLoop (d := rowDialect) (Γ := [RowTy.wide q, RowTy.word, RowTy.row q, RowTy.row q])
      (cs := [RowTy.wide q]) (.there .here) (.cons .here .nil) (rowBody q ζ) (rowTail q))

theorem foldl_range_add {α : Type} [AddCommMonoid α] (g : ℕ → α) :
    ∀ (n : ℕ) (c : α), (List.range n).foldl (fun c i => c + g i) c = c + ∑ i ∈ range n, g i
  | 0, c => by simp
  | n + 1, c => by
    rw [List.range_succ, List.foldl_append, foldl_range_add g n c, Finset.sum_range_succ]
    simp [add_assoc]

/-- **The ring-level row product denotes the sum of the base products.** -/
theorem rowLoop_denote (q : ℕ) (ζ : ZMod q) (fuel : ℕ) (n : BitVec 64)
    (a b : ℕ → ZMod q × ZMod q) :
    (rowLoop q ζ).denote fuel (.cons n (.cons a (.cons b .nil)))
      = some (.cons (∑ j ∈ range n.toNat, bm ζ (a j) (b j) : ZMod q × ZMod q) .nil) := by
  have hf := NFProg.foldlM_single (d := rowDialect) (t := RowTy.wide q)
    (fun acc i => (rowBody q ζ).denote fuel
      (hvAppend acc (.cons (HasWord64.ofNat (d := rowDialect) i)
        (.cons ((0, 0) : ZMod q × ZMod q) (.cons n (.cons a (.cons b .nil)))))))
    (fun (c : ZMod q × ZMod q) i =>
      c + bm ζ (a (BitVec.ofNat 64 i).toNat) (b (BitVec.ofNat 64 i).toNat))
    (fun _ _ => rfl) (List.range n.toNat) (0, 0)
  rw [rowLoop, NFProg.denote_var, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
    Option.bind_some, NFProg.denote_forLoop]
  erw [hf, foldl_range_add (α := ZMod q × ZMod q)]
  refine congrArg (fun x => some (HVector.cons x .nil)) ?_
  show ((0, 0) : ZMod q × ZMod q) +
    ∑ i ∈ range n.toNat, bm ζ (a (BitVec.ofNat 64 i).toNat) (b (BitVec.ofNat 64 i).toNat) = _
  rw [Prod.mk_zero_zero, zero_add]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i < 2 ^ 64 := lt_trans (Finset.mem_range.1 hi) n.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

/-- **The ring-level row product against `basemulF`.** At the pairs of block `c` of the
rows `x`, `y` of polynomials in the NTT domain after `logN − 1` layers, and at the block
root of `ψ`, the two outputs are the sums over the row of `basemulF` at lanes `2 c` and
`2 c + 1`. -/
theorem rowLoop_basemulF (q psi logN : ℕ) (hlog : 0 < logN) (x y : ℕ → Limbs [q] (2 ^ logN))
    (c : ℕ) (hc : 2 * c + 1 < 2 ^ logN) (fuel : ℕ) (n : BitVec 64) :
    (rowLoop q (blockRoot (psi : ZMod q) (logN - 1) c)).denote fuel
      (.cons n (.cons (fun j => (x j ⟨0, by simp⟩ ⟨2 * c, by omega⟩,
          x j ⟨0, by simp⟩ ⟨2 * c + 1, hc⟩))
        (.cons (fun j => (y j ⟨0, by simp⟩ ⟨2 * c, by omega⟩,
          y j ⟨0, by simp⟩ ⟨2 * c + 1, hc⟩)) .nil)))
      = some (.cons
          (∑ j ∈ range n.toNat, basemulF logN (logN - 1) [psi] (x j) (y j) ⟨0, by simp⟩
              ⟨2 * c, by omega⟩,
            ∑ j ∈ range n.toNat, basemulF logN (logN - 1) [psi] (x j) (y j) ⟨0, by simp⟩
              ⟨2 * c + 1, hc⟩) .nil) := by
  rw [rowLoop_denote]
  refine congrArg (fun p => some (HVector.cons p .nil)) ?_
  refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_sum, Prod.snd_sum] <;>
    refine Finset.sum_congr rfl fun j _ => ?_
  all_goals
    rw [basemulF_eq_blockMul_two q psi logN hlog (x j) (y j) (rowLanes (x j) ⟨0, by simp⟩)
      (rowLanes (y j) ⟨0, by simp⟩) (fun t ht => by simp [rowLanes, ht])
      (fun t ht => by simp [rowLanes, ht]), blockMul_two]
  · simp [bm, rowLanes, hc, show 2 * c < 2 ^ logN by omega, Nat.mul_mod_right,
      show 2 * c / 2 = c by omega]
  · have h1 : (2 * c + 1) % 2 = 1 := by omega
    simp [bm, rowLanes, hc, show 2 * c < 2 ^ logN by omega, h1]

/-! ## 3. The word blocks as `NFProg` prefixes -/

/-- A `stackLoad w k` expression: cell `i mod k` of the stack array `A`. -/
def loadE {Γ : Ctxt jasminDialect} (w k : ℕ) (A : Var Γ (JasminTy.stackArr w k))
    (i : Var Γ (JasminTy.reg 64)) : Expr jasminDialect Γ (Rw w) :=
  { op := .stackLoad w k, retTy_eq := rfl, args := .cons A (.cons i .nil) }

/-- Sign extension of `v` from `w` to `2 w` bits, then `k`: the `NFProg` form of `sextK`. -/
def sextN {Γ : Ctxt jasminDialect} {ts : List jasminDialect.Ty} (w : ℕ) (v : Var Γ (Rw w))
    (k : NFProg jasminDialect (X3 w Γ) ts) : NFProg jasminDialect Γ ts :=
  .var (castE w (2 * w) v) <| .var (shlE (2 * w) w .here) <| .var (sarE (2 * w) w .here) k

/-- The product of the sign extensions of `u` and `v`, then `k`: the `NFProg` form of
`prodK`. -/
def prodN {Γ : Ctxt jasminDialect} {ts : List jasminDialect.Ty} (w : ℕ) (u v : Var Γ (Rw w))
    (k : NFProg jasminDialect (X7 w Γ) ts) : NFProg jasminDialect Γ ts :=
  sextN w u <| sextN w (up3 v) <| .var (binE .mul (2 * w) (up3 .here) .here) k

/-- One multiply-accumulate step `acc + sext u · sext v` at `2 w` bits, then `k`: one step of
`macK` as an `NFProg` prefix. -/
def macN {Γ : Ctxt jasminDialect} {ts : List jasminDialect.Ty} (w : ℕ) (acc : Var Γ (Rd w))
    (u v : Var Γ (Rw w)) (k : NFProg jasminDialect (Rd w :: X7 w Γ) ts) :
    NFProg jasminDialect Γ ts :=
  prodN w u v <| .var (binE .add (2 * w) (up7 acc) .here) k

/-- The signed Montgomery reduction of the `2 w`-bit variable `a`, then `k`: the `NFProg`
form of `redK`. -/
def redN {Γ : Ctxt jasminDialect} {ts : List jasminDialect.Ty} (w q qinv : ℕ)
    (a : Var Γ (Rd w)) (k : NFProg jasminDialect (X11 w Γ) ts) : NFProg jasminDialect Γ ts :=
  .var (castE (2 * w) w a) <|
  .var (constE w qinv) <|
  .var (binE .mul w (.there .here) .here) <|
  sextN w .here <|
  .var (constE (2 * w) q) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (binE .sub (2 * w) (.there (.there (up3 (w := w) (.there (.there (.there a)))))) .here) <|
  .var (sarE (2 * w) w .here) <|
  .var (castE (2 * w) w .here) k

/-! ## 4. The word-level loop -/

/-- A stack array of `k` words of `w` bits. -/
abbrev Arr (w k : ℕ) : jasminDialect.Ty := JasminTy.stackArr w k

/-- The context of the word loop: the trip count and the four operand arrays (even and odd
words of the first row, even and odd words of the second row). -/
abbrev WCtx (w k : ℕ) : Ctxt jasminDialect :=
  [JasminTy.reg 64, Arr w k, Arr w k, Arr w k, Arr w k]

/-- The loop body: load the four operand words of trip `i` and add the four products into
the three accumulators (even products, odd products, cross products). -/
def rowBodyW (w k : ℕ) : NFProg jasminDialect
    [Rd w, Rd w, Rd w, JasminTy.reg 64, Rd w, JasminTy.reg 64, Arr w k, Arr w k, Arr w k,
      Arr w k] [Rd w, Rd w, Rd w] :=
  .var (loadE w k (.there (.there (.there (.there (.there (.there .here))))))
    (.there (.there (.there .here)))) <|
  .var (loadE w k (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.there (.there (.there (.there .here))))) <|
  .var (loadE w k (.there (.there (.there (.there (.there (.there (.there (.there (.there
    (.there .here))))))))))
    (.there (.there (.there (.there (.there .here)))))) <|
  .var (loadE w k (.there (.there (.there (.there (.there (.there (.there (.there (.there
    (.there (.there (.there .here))))))))))))
    (.there (.there (.there (.there (.there (.there .here))))))) <|
  macN w (.there (.there (.there (.there .here)))) (.there (.there (.there .here)))
    (.there .here) <|
  macN w (upMac (.there (.there (.there (.there (.there .here))))))
    (upMac (.there (.there .here))) (upMac .here) <|
  macN w (upMac (upMac (.there (.there (.there (.there (.there (.there .here))))))))
    (upMac (upMac (.there (.there (.there .here))))) (upMac (upMac .here)) <|
  macN w .here (upMac (upMac (upMac (.there (.there .here)))))
    (upMac (upMac (upMac (.there .here)))) <|
  .ret (.cons (upMac (upMac (upMac .here))) (.cons (upMac (upMac .here)) (.cons .here .nil)))

/-- The two output reductions: `R(u)` of the head `u` and `R(s₀₁)`. -/
def rowOutW (w q qinv : ℕ) {Γ : Ctxt jasminDialect} (s01 : Var Γ (Rd w)) :
    NFProg jasminDialect (Rd w :: Γ) [Rw w, Rw w] :=
  redN w q qinv .here <|
  redN w q qinv (up11 (.there s01)) <|
  .ret (.cons (up11 .here) (.cons .here .nil))

theorem rowOutW_denote (w q qinv : ℕ) {Γ : Ctxt jasminDialect} (s01 : Var Γ (Rd w))
    (fuel : ℕ) (u : BitVec (2 * w)) (V : Valuation Γ) :
    (rowOutW w q qinv s01).denote fuel (.cons u V)
      = some (.cons (smontAccW w q qinv u : BitVec w)
          (.cons (smontAccW w q qinv (show BitVec (2 * w) from s01.lookup V) : BitVec w)
            .nil)) := rfl

/-- The context after the loop: the three accumulators, the zero word, the trip count and
the four arrays. -/
abbrev TailCtx (w k : ℕ) : Ctxt jasminDialect :=
  [Rd w, Rd w, Rd w, Rd w, JasminTy.reg 64, Arr w k, Arr w k, Arr w k, Arr w k]

/-- The final pass after the inner reduction `r = R(s₁₁)` and its sign extension: the
product with the twiddle constant `z`, the sum with `s₀₀`, and the two output reductions. -/
def rowTailIn (w k z q qinv : ℕ) : NFProg jasminDialect (X3 w (X11 w (TailCtx w k)))
    [Rw w, Rw w] :=
  .var (constE (2 * w) z) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (binE .add (2 * w) (.there (.there (up3 (up11 .here)))) .here) <|
  rowOutW w q qinv (.there (.there (up3 (up11 (.there (.there .here))))))

theorem rowTailIn_denote (w k z q qinv fuel : ℕ) (V : Valuation (X3 w (X11 w (TailCtx w k)))) :
    (rowTailIn w k z q qinv).denote fuel V
      = some (.cons (smontAccW w q qinv
            ((show BitVec (2 * w) from (up3 (w := w) (up11 (w := w) .here)).lookup V)
              + (show BitVec (2 * w) from (Var.here).lookup V) * BitVec.ofNat (2 * w) z) :
            BitVec w)
          (.cons (smontAccW w q qinv (show BitVec (2 * w) from
            (up3 (w := w) (up11 (w := w) (.there (.there .here)))).lookup V) : BitVec w) .nil)) :=
  rfl

theorem sextVal_here {Γ : Ctxt jasminDialect} (w : ℕ) (v : Var Γ (Rw w)) (V : Valuation Γ) :
    (Var.here : Var (X3 w Γ) (Rd w)).lookup (sextVal w v V)
      = sextW (show BitVec w from v.lookup V) := rfl

theorem sextVal_up3 {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (w : ℕ) (v : Var Γ (Rw w))
    (x : Var Γ t) (V : Valuation Γ) : (up3 (w := w) x).lookup (sextVal w v V) = x.lookup V := rfl

theorem redVal_here {Γ : Ctxt jasminDialect} (w q qinv : ℕ) (a : Var Γ (Rd w))
    (V : Valuation Γ) : (Var.here : Var (X11 w Γ) (Rw w)).lookup (redVal w q qinv a V)
      = smontAccW w q qinv (show BitVec (2 * w) from a.lookup V) := rfl

theorem redVal_up11 {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (w q qinv : ℕ)
    (a : Var Γ (Rd w)) (x : Var Γ t) (V : Valuation Γ) :
    (up11 (w := w) x).lookup (redVal w q qinv a V) = x.lookup V := rfl

/-- The final reduction pass: `R(s₀₀ + sext R(s₁₁) · z)` and `R(s₀₁)`. -/
def rowTailW (w k q qinv z : ℕ) : NFProg jasminDialect (TailCtx w k) [Rw w, Rw w] :=
  redN w q qinv (.there .here) <| sextN w .here <| rowTailIn w k z q qinv

/-- **The word-level row product.** From three zero `2 w`-bit accumulators, `n` trips of
`rowBodyW`, then the single reduction pass `rowTailW`. -/
def rowLoopW (w k q qinv z : ℕ) : NFProg jasminDialect (WCtx w k) [Rw w, Rw w] :=
  .var (t := Rd w) (constE (2 * w) 0)
    (NFProg.forLoop (d := jasminDialect)
      (Γ := [Rd w, JasminTy.reg 64, Arr w k, Arr w k, Arr w k, Arr w k])
      (cs := [Rd w, Rd w, Rd w]) (.there .here) (.cons .here (.cons .here (.cons .here .nil)))
      (rowBodyW w k) (rowTailW w k q qinv z))

/-- The ring-level loop body adds the base product of entry `i` of both rows. -/
theorem rowBody_denote (q : ℕ) (ζ : ZMod q) (fuel : ℕ) (c z : ZMod q × ZMod q)
    (i n : BitVec 64) (a b : ℕ → ZMod q × ZMod q) :
    (rowBody q ζ).denote fuel (.cons c (.cons i (.cons z (.cons n (.cons a (.cons b .nil))))))
      = some (.cons (c + bm ζ (a i.toNat) (b i.toNat) : ZMod q × ZMod q) .nil) := rfl

/-- The word loop body adds the four products of trip `i` into the three accumulators. -/
theorem rowBodyW_denote (w k fuel : ℕ) (s00 s11 s01 z : BitVec (2 * w)) (i n : BitVec 64)
    (A0 A1 B0 B1 : Fin k → BitVec w) :
    (rowBodyW w k).denote fuel (.cons s00 (.cons s11 (.cons s01 (.cons i (.cons z (.cons n
        (.cons A0 (.cons A1 (.cons B0 (.cons B1 .nil))))))))))
      = some (.cons (s00 + sextW (stackGet A0 i.toNat) * sextW (stackGet B0 i.toNat) :
            BitVec (2 * w))
          (.cons (s11 + sextW (stackGet A1 i.toNat) * sextW (stackGet B1 i.toNat) :
            BitVec (2 * w))
          (.cons (s01 + sextW (stackGet A0 i.toNat) * sextW (stackGet B1 i.toNat)
              + sextW (stackGet A1 i.toNat) * sextW (stackGet B0 i.toNat) : BitVec (2 * w))
            .nil))) := rfl

theorem sextN_denote {Γ : Ctxt jasminDialect} {ts : List jasminDialect.Ty} (w : ℕ)
    (v : Var Γ (Rw w)) (k : NFProg jasminDialect (X3 w Γ) ts) (fuel : ℕ) (V : Valuation Γ) :
    (sextN w v k).denote fuel V = k.denote fuel (sextVal w v V) := rfl

theorem redN_denote {Γ : Ctxt jasminDialect} {ts : List jasminDialect.Ty} (w q qinv : ℕ)
    (a : Var Γ (Rd w)) (k : NFProg jasminDialect (X11 w Γ) ts) (fuel : ℕ) (V : Valuation Γ) :
    (redN w q qinv a k).denote fuel V = k.denote fuel (redVal w q qinv a V) := rfl

/-- The final reduction pass reduces the twiddled sum, multiplies by the twiddle constant,
adds the even sum and reduces, and reduces the cross sum. -/
theorem rowTailW_denote (w k q qinv z fuel : ℕ) (s00 s11 s01 z0 : BitVec (2 * w))
    (n : BitVec 64) (A0 A1 B0 B1 : Fin k → BitVec w) :
    (rowTailW w k q qinv z).denote fuel (.cons s00 (.cons s11 (.cons s01 (.cons z0 (.cons n
        (.cons A0 (.cons A1 (.cons B0 (.cons B1 .nil)))))))))
      = some (.cons (smontAccW w q qinv
            (s00 + sextW (smontAccW w q qinv s11) * BitVec.ofNat (2 * w) z) : BitVec w)
          (.cons (smontAccW w q qinv s01 : BitVec w) .nil)) := by
  rw [rowTailW, redN_denote, sextN_denote, rowTailIn_denote, sextVal_up3, sextVal_up3,
    sextVal_here, redVal_up11, redVal_up11, redVal_here]
  rfl

/-! ## 5. The wide representation -/

/-- **The wide representation at grade `B`.** Three `2 w`-bit words represent the wide
accumulator `c` modulo `q` at the twiddle `ζ`: the even sum `s₀₀` and the odd sum `s₁₁` are
at most `B`, the cross sum `s₀₁` at most `2 B` in absolute value, `s₀₀ + s₁₁ · ζ = c.1` and
`s₀₁ = c.2` modulo `q`. -/
def WideRep (q w : ℕ) (ζ : ZMod q) (B : ℕ) (c : ZMod q × ZMod q)
    (s00 s11 s01 : BitVec (2 * w)) : Prop :=
  |s00.toInt| ≤ B ∧ |s11.toInt| ≤ B ∧ |s01.toInt| ≤ 2 * B ∧
    ((s00.toInt : ℤ) : ZMod q) + ((s11.toInt : ℤ) : ZMod q) * ζ = c.1 ∧
    ((s01.toInt : ℤ) : ZMod q) = c.2

/-- The zero accumulators represent the zero wide accumulator at grade `0`. -/
theorem wideRep_zero (q w : ℕ) (ζ : ZMod q) :
    WideRep q w ζ 0 (0, 0) (0 : BitVec (2 * w)) 0 0 := by
  simp [WideRep]

/-- The product of two sign-extended words is exact inside the accumulator. -/
theorem sextMul_toInt {w : ℕ} (x y : BitVec w) {A B : ℕ} (hx : |x.toInt| ≤ A)
    (hy : |y.toInt| ≤ B) (hfit : 2 * (A * B) < 2 ^ (2 * w)) :
    (sextW x * sextW y).toInt = x.toInt * y.toInt ∧ |x.toInt * y.toInt| ≤ ((A * B : ℕ) : ℤ) := by
  have hp : |x.toInt * y.toInt| ≤ ((A * B : ℕ) : ℤ) := by
    rw [abs_mul]; push_cast; exact mul_le_mul hx hy (abs_nonneg _) (by positivity)
  have hf : (2 * ((A * B : ℕ) : ℤ)) < ((2 ^ (2 * w) : ℕ) : ℤ) := by exact_mod_cast hfit
  refine ⟨?_, hp⟩
  rw [toInt_mul_exact _ _ (by rw [sextW_toInt, sextW_toInt]; linarith), sextW_toInt, sextW_toInt]

/-- **One multiply-accumulate trip.** On operand words representing the pairs `a`, `b` with
factor `1` and bounds `inA`, `inB`, adding the four products into accumulators at grade `G`
gives accumulators at grade `G + inA · inB` representing `c + bm ζ a b`, provided four
times the new grade fits the `2 w`-bit accumulator. -/
theorem wideRep_step {q w : ℕ} {ζ : ZMod q} {G inA inB : ℕ}
    (hfit : 2 * (2 * (G + inA * inB)) < 2 ^ (2 * w)) {c : ZMod q × ZMod q}
    {s00 s11 s01 : BitVec (2 * w)} (h : WideRep q w ζ G c s00 s11 s01)
    {x0 x1 y0 y1 : BitVec w} {a b : ZMod q × ZMod q}
    (hx0 : SRep q w 1 inA a.1 x0) (hx1 : SRep q w 1 inA a.2 x1)
    (hy0 : SRep q w 1 inB b.1 y0) (hy1 : SRep q w 1 inB b.2 y1) :
    WideRep q w ζ (G + inA * inB) (c + bm ζ a b) (s00 + sextW x0 * sextW y0)
      (s11 + sextW x1 * sextW y1) (s01 + sextW x0 * sextW y1 + sextW x1 * sextW y0) := by
  obtain ⟨h00, h11, h01, e1, e2⟩ := h
  have hf : (2 * (2 * ((G : ℤ) + (inA * inB : ℕ)))) < ((2 ^ (2 * w) : ℕ) : ℤ) := by
    exact_mod_cast hfit
  have hAB : 2 * (inA * inB) < 2 ^ (2 * w) := by omega
  obtain ⟨p00, b00⟩ := sextMul_toInt x0 y0 hx0.1 hy0.1 hAB
  obtain ⟨p11, b11⟩ := sextMul_toInt x1 y1 hx1.1 hy1.1 hAB
  obtain ⟨p01, b01⟩ := sextMul_toInt x0 y1 hx0.1 hy1.1 hAB
  obtain ⟨p10, b10⟩ := sextMul_toInt x1 y0 hx1.1 hy0.1 hAB
  have hG : (0 : ℤ) ≤ G := Int.natCast_nonneg _
  have hP : (0 : ℤ) ≤ ((inA * inB : ℕ) : ℤ) := Int.natCast_nonneg _
  have t00 := abs_add_le s00.toInt (x0.toInt * y0.toInt)
  have t11 := abs_add_le s11.toInt (x1.toInt * y1.toInt)
  have t01 := abs_add_le s01.toInt (x0.toInt * y1.toInt)
  have t01' := abs_add_le (s01.toInt + x0.toInt * y1.toInt) (x1.toInt * y0.toInt)
  have a00 : (s00 + sextW x0 * sextW y0).toInt = s00.toInt + x0.toInt * y0.toInt := by
    rw [toInt_add_exact _ _ (by rw [p00]; linarith), p00]
  have a11 : (s11 + sextW x1 * sextW y1).toInt = s11.toInt + x1.toInt * y1.toInt := by
    rw [toInt_add_exact _ _ (by rw [p11]; linarith), p11]
  have a01 : (s01 + sextW x0 * sextW y1).toInt = s01.toInt + x0.toInt * y1.toInt := by
    rw [toInt_add_exact _ _ (by rw [p01]; linarith), p01]
  have a01' : (s01 + sextW x0 * sextW y1 + sextW x1 * sextW y0).toInt
      = s01.toInt + x0.toInt * y1.toInt + x1.toInt * y0.toInt := by
    rw [toInt_add_exact _ _ (by rw [a01, p10]; linarith), a01, p10]
  have ex0 := hx0.2; have ex1 := hx1.2; have ey0 := hy0.2; have ey1 := hy1.2
  rw [mul_one] at ex0 ex1 ey0 ey1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [a00]; push_cast at b00 ⊢; linarith
  · rw [a11]; push_cast at b11 ⊢; linarith
  · rw [a01']; push_cast at b01 b10 ⊢; linarith
  · show _ = c.1 + (a.1 * b.1 + a.2 * b.2 * ζ)
    rw [a00, a11, ← e1, ← ex0, ← ex1, ← ey0, ← ey1]
    push_cast; ring
  · show _ = c.2 + (a.1 * b.2 + a.2 * b.1)
    rw [a01', ← e2, ← ex0, ← ex1, ← ey0, ← ey1]
    push_cast; ring

/-- **The final reduction pass.** Under `AccSched.Ok k`, accumulators at grade
`k · inA · inB` representing the wide accumulator `c`, a twiddle constant `z` reading `ζM`
with `2 |ζM| ≤ q` and `ζM = ζ · 2 ^ w` modulo `q`: the two output words represent `c.1` and
`c.2` with factor `2 ^ w` within `outB`. -/
theorem wideRep_final (S : AccSched) (k : ℕ) (hS : S.Ok k) (ζ : ZMod S.q) (z : ℕ) (ζM : ℤ)
    (hz : (BitVec.ofNat (2 * S.w) z).toInt = ζM) (hζ : 2 * |ζM| ≤ S.q)
    (hζc : (ζM : ZMod S.q) = ζ * ((2 ^ S.w : ℕ) : ZMod S.q)) {c : ZMod S.q × ZMod S.q}
    {s00 s11 s01 : BitVec (2 * S.w)} (h : WideRep S.q S.w ζ (k * (S.inA * S.inB)) c s00 s11 s01) :
    SRep S.q S.w ((2 ^ S.w : ℕ) : ZMod S.q) S.outB c.1
        (smontAccW S.w S.q S.qinv
          (s00 + sextW (smontAccW S.w S.q S.qinv s11) * BitVec.ofNat (2 * S.w) z)) ∧
      SRep S.q S.w ((2 ^ S.w : ℕ) : ZMod S.q) S.outB c.2 (smontAccW S.w S.q S.qinv s01) := by
  obtain ⟨b00, b11, b01, e1, e2⟩ := h
  push_cast at b00 b11 b01
  obtain ⟨⟨eo0, bo0⟩, eo1, bo1⟩ := accTail_spec S k hS z ζM hz hζ s00 s11 s01 b00 b11 b01
  have hr2 := smont_mul_radix S.w S.q S.qinv hS.1 s11.toInt
  refine ⟨⟨by rw [eo0]; exact bo0, ?_⟩, ⟨by rw [eo1]; exact bo1,
    by rw [eo1, smont_mul_radix _ _ _ hS.1, e2]⟩⟩
  rw [eo0, smont_mul_radix _ _ _ hS.1, ← e1]
  push_cast
  linear_combination (smont S.w S.q S.qinv s11.toInt : ZMod S.q) * hζc + ζ * hr2

/-! ## 6. The two loops related -/

/-- The input relation: for `j < k`, entry `j` of the first row is represented with factor
`1` and bound `inA` by cell `j` of `A0` (first coordinate) and `A1` (second coordinate), and
entry `j` of the second row with bound `inB` by `B0` and `B1`. -/
def RowIn (S : AccSched) (k : ℕ) (a b : ℕ → ZMod S.q × ZMod S.q)
    (A0 A1 B0 B1 : Fin k → BitVec S.w) : Prop :=
  ∀ j, j < k →
    SRep S.q S.w 1 S.inA (a j).1 (stackGet A0 j) ∧ SRep S.q S.w 1 S.inA (a j).2 (stackGet A1 j) ∧
    SRep S.q S.w 1 S.inB (b j).1 (stackGet B0 j) ∧ SRep S.q S.w 1 S.inB (b j).2 (stackGet B1 j)

/-- The output relation: the two output words represent the two coordinates of the pair
with factor `2 ^ w` within `outB`. -/
def RowOut (S : AccSched) (p : Valuation ([RowTy.pair S.q] : Ctxt rowDialect))
    (W : Valuation ([Rw S.w, Rw S.w] : Ctxt jasminDialect)) : Prop :=
  SRep S.q S.w ((2 ^ S.w : ℕ) : ZMod S.q) S.outB (show ZMod S.q × ZMod S.q from p.head).1
      (show BitVec S.w from W.head) ∧
    SRep S.q S.w ((2 ^ S.w : ℕ) : ZMod S.q) S.outB (show ZMod S.q × ZMod S.q from p.head).2
      (show BitVec S.w from W.tail.head)

/-- **The row product, ring level against word level.** Under `AccSched.Ok k`, at a trip
count `k`, on input arrays related to the rows by `RowIn` and a twiddle constant `z`
reading `ζM ≡ ζ · 2 ^ w` with `2 |ζM| ≤ q`, the ring-level loop `rowLoop` and the word loop
`rowLoopW` return `RowOut`-related results. The carried relation at trip `j` is
`WideRep (j · inA · inB)`. -/
theorem rowLoop_rel (S : AccSched) (k : ℕ) (hS : S.Ok k) (ζ : ZMod S.q) (z : ℕ) (ζM : ℤ)
    (hz : (BitVec.ofNat (2 * S.w) z).toInt = ζM) (hζ : 2 * |ζM| ≤ S.q)
    (hζc : (ζM : ZMod S.q) = ζ * ((2 ^ S.w : ℕ) : ZMod S.q)) (fuel fuel' : ℕ)
    (n : BitVec 64) (hn : n.toNat = k) (a b : ℕ → ZMod S.q × ZMod S.q)
    (A0 A1 B0 B1 : Fin k → BitVec S.w) (hin : RowIn S k a b A0 A1 B0 B1) :
    Option.Rel (RowOut S)
      ((rowLoop S.q ζ).denote fuel (.cons n (.cons a (.cons b .nil))))
      ((rowLoopW S.w k S.q S.qinv z).denote fuel'
        (.cons n (.cons A0 (.cons A1 (.cons B0 (.cons B1 .nil)))))) := by
  have hk2 := accSched_ok_fit hS
  have key := NFProg.denote_forLoop_rel_graded (d := rowDialect) (d' := jasminDialect)
    fuel fuel'
    (RΓ := fun V V' =>
      V = (.cons ((0, 0) : ZMod S.q × ZMod S.q) (.cons n (.cons a (.cons b .nil))) :
        Valuation ([RowTy.wide S.q, RowTy.word, RowTy.row S.q, RowTy.row S.q] : Ctxt rowDialect)) ∧
      V' = (.cons (0 : BitVec (2 * S.w))
          (.cons n (.cons A0 (.cons A1 (.cons B0 (.cons B1 .nil))))) :
        Valuation ([Rd S.w, JasminTy.reg 64, Arr S.w k, Arr S.w k, Arr S.w k, Arr S.w k] :
          Ctxt jasminDialect)))
    (Rc := fun j A W => WideRep S.q S.w ζ (j * (S.inA * S.inB))
      (show ZMod S.q × ZMod S.q from A.head) (show BitVec (2 * S.w) from W.head)
      (show BitVec (2 * S.w) from W.tail.head) (show BitVec (2 * S.w) from W.tail.tail.head))
    (S := RowOut S)
    (.there .here) (.cons .here .nil) (rowBody S.q ζ) (rowTail S.q)
    (.there .here) (.cons .here (.cons .here (.cons .here .nil))) (rowBodyW S.w k)
    (rowTailW S.w k S.q S.qinv z)
    ?hcount ?hinits ?hbody ?hk _ _ ⟨rfl, rfl⟩
  case hcount =>
    rintro _ _ ⟨rfl, rfl⟩
    rfl
  case hinits =>
    rintro _ _ ⟨rfl, rfl⟩
    show WideRep S.q S.w ζ (0 * (S.inA * S.inB)) (0, 0) 0 0 0
    rw [Nat.zero_mul]
    exact wideRep_zero _ _ _
  case hbody =>
    rintro _ _ ⟨rfl, rfl⟩ i hi A A' hA
    change i < n.toNat at hi
    rcases A with _ | ⟨c, _ | _⟩
    rcases A' with _ | ⟨s00, _ | ⟨s11, _ | ⟨s01, _ | _⟩⟩⟩
    change WideRep S.q S.w ζ (i * (S.inA * S.inB)) c s00 s11 s01 at hA
    have hi64 : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans hi n.isLt)]
    erw [rowBody_denote S.q ζ fuel c (0, 0) (BitVec.ofNat 64 i) n a b,
      rowBodyW_denote S.w k fuel' s00 s11 s01 0 (BitVec.ofNat 64 i) n A0 A1 B0 B1]
    refine Option.Rel.some ?_
    show WideRep S.q S.w ζ ((i + 1) * (S.inA * S.inB)) _ _ _ _
    rw [hi64, Nat.succ_mul]
    rw [hn] at hi
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hin i hi
    have hle : (i + 1) * (S.inA * S.inB) ≤ k * (S.inA * S.inB) := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at hle
    exact wideRep_step (by omega) hA hx0 hx1 hy0 hy1
  case hk =>
    rintro _ _ ⟨rfl, rfl⟩ A A' hA
    rcases A with _ | ⟨c, _ | _⟩
    rcases A' with _ | ⟨s00, _ | ⟨s11, _ | ⟨s01, _ | _⟩⟩⟩
    change WideRep S.q S.w ζ (n.toNat * (S.inA * S.inB)) c s00 s11 s01 at hA
    rw [hn] at hA
    erw [rowTailW_denote S.w k S.q S.qinv z fuel' s00 s11 s01 0 n A0 A1 B0 B1]
    exact Option.Rel.some (wideRep_final S k hS ζ z ζM hz hζ hζc hA)
  exact key

/-- **The row product at ML-KEM `k = 3`.** With the certificate `mlkemAcc3_ok`, block `c`
after `L` layers at the root `ψ`, the twiddle constant `cEnc 16 (zetaM 16 3329 ψ L c)`: the
ring-level loop at the block root and the word loop return `RowOut`-related results. -/
theorem mlkemRow3_rel (psi L c fuel fuel' : ℕ) (n : BitVec 64) (hn : n.toNat = 3)
    (a b : ℕ → ZMod mlkemAcc3.q × ZMod mlkemAcc3.q) (A0 A1 B0 B1 : Fin 3 → BitVec mlkemAcc3.w)
    (hin : RowIn mlkemAcc3 3 a b A0 A1 B0 B1) :
    Option.Rel (RowOut mlkemAcc3)
      ((rowLoop mlkemAcc3.q (blockRoot (psi : ZMod mlkemAcc3.q) L c)).denote fuel
        (.cons n (.cons a (.cons b .nil))))
      ((rowLoopW mlkemAcc3.w 3 mlkemAcc3.q mlkemAcc3.qinv
          (cEnc mlkemAcc3.w (zetaM mlkemAcc3.w mlkemAcc3.q psi L c))).denote fuel'
        (.cons n (.cons A0 (.cons A1 (.cons B0 (.cons B1 .nil)))))) :=
  rowLoop_rel mlkemAcc3 3 mlkemAcc3_ok _ _ _
    (cEnc_toInt _ _ _ (zetaM_abs _ _ psi L c (by decide)) (by decide))
    (zetaM_abs _ _ psi L c (by decide)) (by rw [zetaM_cast]; push_cast; rfl)
    fuel fuel' n hn a b A0 A1 B0 B1 hin

end CatCrypt.Crypto.SecureCompilation.VIR.RowLazy
