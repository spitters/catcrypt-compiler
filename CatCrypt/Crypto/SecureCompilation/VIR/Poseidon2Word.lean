/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NarrowFieldZk
public import CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord
public import CatCrypt.Crypto.Hash.Poseidon2.Width16
public import CatCrypt.Crypto.Hash.Poseidon2.BabyBear
public import CatCrypt.Crypto.Hash.Poseidon2.KoalaBear
public import CatCrypt.Crypto.SecureCompilation.VIR.BoundSched

/-!
# The Poseidon2 layers at width 16 on narrow words

`jasminDialect` programs for the three building blocks of the width-16 Poseidon2
permutation of `Hash.Poseidon2.Width16` on `w`-bit words, with denotation theorems
against the field-level functions `sbox`, `externalMDS` and `internalMDS`.

* **S-box.** `sboxProg M bits` raises its input to the power `nexp bits 0 + 1` by squarings
  and multiplications by the input, each a call of the two-input block of a `ChainMul`.
  A `ChainMul` is a block with one bound that is both its input and output bound and a
  constant `κ` with `z · κ = x · y` for its output `z`; it is built from the Plantard,
  Montgomery or Barrett block of a `WordField`, or from the Mersenne fold block. The output
  `z` of the S-box satisfies `z · κ ^ (d − 1) = x ^ d`, so in the representation
  `x ≡ u · κ` it represents `u ^ d`.
* **External layer.** `extProg` computes lane `i` by `extBlk` on twenty input lanes read
  through `extIdx i`: the `circ(2, 3, 1, 1)` row at position `i mod 4` of each of the four
  groups and of the group of `i`, their column sum, and one Barrett reduction. The rows
  and the sum are accumulated at `2 w` bits without reduction.
* **Internal layer.** `intProg` computes lane `i` by `intBlk`: the sum of the sixteen
  lanes plus the diagonal constant times lane `i`, accumulated at `2 w` bits, and one
  Barrett reduction.

* **Permutation.** `permProg` composes the blocks along the rounds of `permute`: the
  initial external layer, then per round the S-box layer (every lane, or lane 0) and the
  linear layer of the round. The constant vector of the next round is folded into each
  linear layer before its reduction (`extRcBlk`, `intRcBlk`), so the S-box reads the layer
  output directly. The internal lane reduces the diagonal product `d · x` once before the
  sum. Lanes stay at most one bound `B` across rounds (`RcRed.Ok`); at BabyBear and
  KoalaBear `B = p + 64`, with Plantard S-box chains on inputs at most `B`. Lanes represent
  the state `u` as `u · κ` with the chain constant `κ = −2 ^ 64`, and the constants enter
  as residues of `c · κ`.

Each block is closed and lies in the exact fragment of `ComRangeExact`; its side condition
is a bounds check `boundsOk` decided by `decide +kernel`, which gives the output bound,
and its algebraic theorem is stated over its integer semantics. A closed block is called
by renaming it into the caller's context (`homOf`) and splicing its bindings in front of a
continuation (`spliceK`).

## Main definitions

* `spliceK`, `homOf`: splicing a program into a continuation, and the renaming of a
  closed block's inputs to variables of the caller.
* `ChainMul`, `plantChain`, `montChain`, `barChain`, `foldChain`: chainable multiply
  blocks.
* `bbSboxChain`, `kbSboxChain`, `m31SboxChain`: the chains at BabyBear, KoalaBear
  (Plantard, input bound `p`) and Mersenne-31 (fold, input bound `2 ^ 31`).
* `powK`, `sboxProg`, `nexp`: the square-and-multiply schedule.
* `rowK`, `redK`, `extBlk`, `intBlk`: the row, the reduction and the two lane blocks.
* `extProg`, `intProg`: the two linear layers on sixteen lanes.
* `LinRed`, `LinRed.extOk`, `LinRed.intOk`: the reduction constants and output bounds of
  the linear layers and their decidable side conditions.
* `bbLin`, `kbLin`: the instances at BabyBear and KoalaBear, input bound `p`.
* `extRcBlk`, `intRcBlk`, `extRcProg`, `intRcProg`: the linear layers with a folded
  constant; `RcRed`, `RcRed.Ok`: their constants and the cross-round bound check.
* `Rep16`, `encC`: the representation of a state by sixteen lanes, and the constants.
* `sboxLayerProg`, `Step`, `steps`, `roundProg`, `roundsProg`, `permProg`: the S-box
  layer, the rounds of `permute`, and the permutation program.
* `bbParams`: the BabyBear parameters of `Width16` from the constants of
  `Hash.Poseidon2.BabyBear`; `bbRc`, `kbRc`, `bbPermChain`, `kbPermChain`: the instances
  with lanes at most `p + 64`.

## Main results

* `spliceK_denote`, `pullV_homOf`: the denotation of a splice and of a renamed call.
* `sboxProg_spec`, `sboxProg_sbox`: the S-box output is at most the chain bound and
  represents the S-box of the input.
* `bbSbox_spec`, `kbSbox_spec`: the S-box at BabyBear (degree 7) and KoalaBear (degree 3).
* `mdsPre_apply`, `externalMDS_eq`: the external layer as rotated rows.
* `extProg_spec`: every output lane of `extProg` is at most `extOut` and is the lane of
  `externalMDS` modulo `p`.
* `intProg_spec`: every output lane of `intProg` is at most `intOut` and is the lane of
  `internalMDS` modulo `p`.
* `bbLin_extOk`, `bbLin_intOk`, `kbLin_extOk`, `kbLin_intOk`: the instance certificates;
  with `babyBearFieldP_plantOk` (S-box degree 7) and `koalaBearFieldP_plantOk` (degree 3)
  they cover the three blocks at both fields.
* `extRcProg_rep`, `intRcProg_rep`, `sboxLayerProg_rep`, `roundProg_rep`: the layers and
  one round on represented states.
* `permute_eq_steps`: `permute` is the fold of `steps` from the initial external layer.
* `permProg_spec`: under `RcRed.Ok` at the chain bound, the output lanes of `permProg`
  represent `permute P` of the state the input lanes represent.
* `bbFieldB_plantOk`, `kbFieldB_plantOk`, `bbRc_ok`, `kbRc_ok`: the certificates that the
  bound `p + 64` closes; `bbPermProg_spec`, `kbPermProg_spec`: the two instances.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Word

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
open CatCrypt.Crypto.SecureCompilation.VIR.NarrowField
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate (constE binE castE shrE Rw Ctxs
  laneVarG lanesVal hvGetG laneVarG_lookup hvGetG_denoteN)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV pullV_id
  Com.denote_rename Var.lookup_rename)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (pullV_comp)
open CatCrypt.Crypto.SecureCompilation.VIR.MergeComDenote (pullV_tail)
open CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord (laneMapW laneMapW_denote)
open CatCrypt.Crypto.Hash.Poseidon2.Width16 (Params sbox externalMDS internalMDS mdsPre
  colSumMap mat4 sumAll permute externalRound internalRound rcInitial rcFinal)

/-! ## 1. Splicing and calls -/

/-- Emit the bindings of `c`, then `k` at the variable holding its result. -/
def spliceK {t : JasminTy} :
    {Γ : JCtxt} → {τ : JasminTy} → Com jasminDialect Γ τ →
    (∀ {Γ' : JCtxt}, Ctxt.Hom Γ Γ' → Var Γ' τ → Com jasminDialect Γ' t) →
    Com jasminDialect Γ t
  | _, _, .ret v, k => k (Ctxt.Hom.id _) v
  | _, _, .var (t := bs) e body, k =>
      .var e (spliceK body (fun {_} h v => k (h.comp (Ctxt.Hom.weakenOne _ bs)) v))

/-- The continuation of `spliceK c k` is called at an extension of the context, at a
valuation pulling back to `V`, and at a variable holding `c.denote V`: a property of every
such call holds of the splice. -/
theorem spliceK_denote {t : JasminTy} (Q : ⟦t⟧ → Prop) :
    ∀ {Γ : JCtxt} {τ : JasminTy} (c : Com jasminDialect Γ τ) (V : Valuation Γ)
      (k : ∀ {Γ' : JCtxt}, Ctxt.Hom Γ Γ' → Var Γ' τ → Com jasminDialect Γ' t),
      (∀ {Γ' : JCtxt} (h : Ctxt.Hom Γ Γ') (v : Var Γ' τ) (V' : Valuation Γ'),
          pullV h V' = V → v.lookup V' = c.denote V → Q ((k h v).denote V')) →
      Q ((spliceK c k).denote V)
  | _, _, .ret v, V, k, hk => hk (Ctxt.Hom.id _) v V (pullV_id V) rfl
  | _, _, .var e body, V, k, hk => by
      refine spliceK_denote Q body (V.extend (e.denote V)) _ ?_
      intro Γ' h v V' hV hv
      exact hk (Ctxt.Hom.comp h (Ctxt.Hom.weakenOne _ _)) v V' (pullV_tail h V' V hV) hv

/-- The renaming that sends input `j` of a closed block to entry `j` of `vs`. -/
def homOf {Γ Δ : JCtxt} (vs : HVector (fun t => Var Γ t) Δ) : Ctxt.Hom Δ Γ :=
  fun v => hget vs v

theorem pullV_homOf {Γ : JCtxt} (V : Valuation Γ) :
    ∀ {Δ : JCtxt} (vs : HVector (fun t => Var Γ t) Δ),
      pullV (homOf vs) V = MultiReturnCom.lookupVars vs V
  | [], .nil => rfl
  | _ :: _, .cons _ vs => congrArg (HVector.cons _) (pullV_homOf V vs)

/-- The word a `w`-bit variable holds. -/
abbrev bv {w : ℕ} {Γ : JCtxt} (v : Var Γ (Rw w)) (V : Valuation Γ) : BitVec w := v.lookup V

/-- The variables `f off, …, f (off + n − 1)`. -/
def lanesHV {Γ : JCtxt} {τ : JasminTy} (f : ℕ → Var Γ τ) :
    (n off : ℕ) → HVector (fun t => Var Γ t) (List.replicate n τ)
  | 0, _ => .nil
  | n + 1, off => .cons (f off) (lanesHV f n (off + 1))

theorem lookupVars_lanesHV {Γ : JCtxt} {τ : JasminTy} (f : ℕ → Var Γ τ) (V : Valuation Γ) :
    ∀ (n off : ℕ), MultiReturnCom.lookupVars (lanesHV f n off) V
      = lanesVal (d := jasminDialect) τ (fun j => (f j).lookup V) n off
  | 0, _ => rfl
  | n + 1, off => congrArg (HVector.cons _) (lookupVars_lanesHV f V n (off + 1))

/-- Lane `j` of the sixteen-lane context. -/
abbrev ln (w j : ℕ) : Var (Ctxs w 16) (Rw w) := laneVarG (Rw w) 15 j

theorem ln_lookup (w : ℕ) (g : ℕ → BitVec w) {j : ℕ} (hj : j ≤ 15) :
    bv (ln w j) (lanesVal (Rw w) g 16 0) = g j := by
  have := laneVarG_lookup (Rw w) g 15 j 0 hj
  rw [Nat.zero_add] at this
  exact this

/-! ## 2. Chainable multiplies and the S-box -/

/-- A two-input block with one bound `bound` for its inputs and its output, whose output
`z` on `x`, `y` satisfies `z · κ = x · y` modulo `p`. -/
structure ChainMul (w p : ℕ) where
  /-- The block. -/
  blk : Com jasminDialect (C2 w) (Rw w)
  /-- The input and output bound. -/
  bound : ℕ
  /-- The scaling constant. -/
  κ : ZMod p
  /-- The output bound and the scaled product. -/
  spec : ∀ x y : BitVec w, x.toNat ≤ bound → y.toNat ≤ bound →
    (run2 blk x y).toNat ≤ bound ∧ ((run2 blk x y).toNat : ZMod p) * κ = x.toNat * y.toNat

/-- The Plantard block as a chainable multiply, `κ = −2 ^ (2 w)`, when its output bound `p`
is at most the input bound. -/
def plantChain {w p : ℕ} (F : WordField w p) (h : F.plantOk = true)
    (hp : p ≤ F.inMax) : ChainMul w p where
  blk := plantBlk w p F.plantInv
  bound := F.inMax
  κ := -2 ^ (2 * w)
  spec x y hx hy := by
    obtain ⟨⟨hle, -⟩, e⟩ := F.mulPlant_rep h (x := x) (y := y) (u := x.toNat) (v := y.toNat)
      ⟨hx, rfl⟩ ⟨hy, rfl⟩
    refine ⟨hle.trans hp, ?_⟩
    have e' := congrArg Neg.neg e
    simp only [neg_neg] at e'
    rw [← e']
    simp [WordField.mulPlant]

/-- The Montgomery block as a chainable multiply, `κ = 2 ^ w`, when its output bound is at
most its input bound. -/
def montChain {w p : ℕ} (F : WordField w p) (h : F.montOk = true)
    (hle : F.montOut ≤ F.inMax) : ChainMul w p where
  blk := montBlk w p F.montInv
  bound := F.inMax
  κ := 2 ^ w
  spec x y hx hy := by
    obtain ⟨⟨hb, -⟩, e⟩ := F.mulMont_rep h (x := x) (y := y) (u := x.toNat) (v := y.toNat)
      ⟨hx, rfl⟩ ⟨hy, rfl⟩
    exact ⟨hb.trans hle, e⟩

/-- The Barrett block as a chainable multiply, `κ = 1`, when its output bound is at most
its input bound. -/
def barChain {w p : ℕ} (F : WordField w p) (h : F.barOk = true)
    (hle : F.barOut ≤ F.inMax) : ChainMul w p where
  blk := barBlk w p F.barS F.barT F.barM
  bound := F.inMax
  κ := 1
  spec x y hx hy := by
    obtain ⟨hb, e⟩ := F.mulBar_rep h (x := x) (y := y) (u := x.toNat) (v := y.toNat)
      ⟨hx, rfl⟩ ⟨hy, rfl⟩
    exact ⟨hb.trans hle, by rw [mul_one]; exact e⟩

section Sbox

variable {w p : ℕ} (M : ChainMul w p)

/-- A call of the block of `M` on `a`, `b`, then `k`. -/
def mulK {Γ : JCtxt} {t : JasminTy} (a b : Var Γ (Rw w))
    (k : ∀ {Γ' : JCtxt}, Ctxt.Hom Γ Γ' → Var Γ' (Rw w) → Com jasminDialect Γ' t) :
    Com jasminDialect Γ t :=
  spliceK (M.blk.rename (homOf (.cons a (.cons b .nil)))) k

theorem mulK_denote {Γ : JCtxt} {t : JasminTy} (Q : ⟦t⟧ → Prop) (a b : Var Γ (Rw w))
    (k : ∀ {Γ' : JCtxt}, Ctxt.Hom Γ Γ' → Var Γ' (Rw w) → Com jasminDialect Γ' t)
    (V : Valuation Γ)
    (hk : ∀ {Γ' : JCtxt} (h : Ctxt.Hom Γ Γ') (v : Var Γ' (Rw w)) (V' : Valuation Γ'),
      pullV h V' = V → bv v V' = run2 M.blk (bv a V) (bv b V) → Q ((k h v).denote V')) :
    Q ((mulK M a b k).denote V) := by
  refine spliceK_denote Q _ V k fun h v V' hV hv => hk h v V' hV ?_
  show v.lookup V' = _
  rw [hv, Com.denote_rename, pullV_homOf]
  rfl

/-- The square-and-multiply schedule: for each digit, square the accumulator, and for a
digit `true` multiply it by `x`; then `k` at the accumulator. -/
def powK {t : JasminTy} : List Bool → {Γ : JCtxt} → Var Γ (Rw w) → Var Γ (Rw w) →
    (∀ {Γ' : JCtxt}, Ctxt.Hom Γ Γ' → Var Γ' (Rw w) → Com jasminDialect Γ' t) →
    Com jasminDialect Γ t
  | [], _, _, acc, k => k (Ctxt.Hom.id _) acc
  | b :: bs, _, x, acc, k =>
    mulK M acc acc fun h1 s =>
      if b then
        mulK M (h1 x) s fun h2 m =>
          powK bs (h2 (h1 x)) m fun h3 r => k (Ctxt.Hom.comp h3 (Ctxt.Hom.comp h2 h1)) r
      else powK bs (h1 x) s fun h3 r => k (Ctxt.Hom.comp h3 h1) r

/-- The exponent minus one after the digits `bs`, from the exponent `n + 1`: a digit
`false` doubles the exponent, a digit `true` doubles it and adds one. -/
def nexp : List Bool → ℕ → ℕ
  | [], n => n
  | b :: bs, n => nexp bs (if b then 2 * n + 2 else 2 * n + 1)

/-- One step of the chain invariant `a · κ ^ n = X ^ (n + 1)`. -/
theorem chain_mul {X a b z κ : ZMod p} {n m : ℕ} (ha : a * κ ^ n = X ^ (n + 1))
    (hb : b * κ ^ m = X ^ (m + 1)) (hz : z * κ = a * b) :
    z * κ ^ (n + m + 1) = X ^ (n + m + 1 + 1) := by
  calc z * κ ^ (n + m + 1) = (z * κ) * κ ^ n * κ ^ m := by ring
    _ = (a * κ ^ n) * (b * κ ^ m) := by rw [hz]; ring
    _ = X ^ (n + m + 1 + 1) := by rw [ha, hb]; ring

theorem powK_denote {t : JasminTy} (Q : ⟦t⟧ → Prop) : ∀ (bs : List Bool) {Γ : JCtxt}
    (x acc : Var Γ (Rw w))
    (k : ∀ {Γ' : JCtxt}, Ctxt.Hom Γ Γ' → Var Γ' (Rw w) → Com jasminDialect Γ' t)
    (V : Valuation Γ) (n : ℕ), (bv x V).toNat ≤ M.bound →
    (bv acc V).toNat ≤ M.bound →
    ((bv acc V).toNat : ZMod p) * M.κ ^ n = ((bv x V).toNat : ZMod p) ^ (n + 1) →
    (∀ {Γ' : JCtxt} (h : Ctxt.Hom Γ Γ') (v : Var Γ' (Rw w)) (V' : Valuation Γ'),
      pullV h V' = V → (bv v V').toNat ≤ M.bound →
      ((bv v V').toNat : ZMod p) * M.κ ^ nexp bs n
        = ((bv x V).toNat : ZMod p) ^ (nexp bs n + 1) → Q ((k h v).denote V')) →
    Q ((powK M bs x acc k).denote V)
  | [], _, x, acc, k, V, n, _, hacc, hinv, hk => hk (Ctxt.Hom.id _) acc V (pullV_id V) hacc hinv
  | b :: bs, _, x, acc, k, V, n, hx, hacc, hinv, hk => by
    refine mulK_denote M Q acc acc _ V fun h1 s V1 hV1 hs => ?_
    obtain ⟨hsb, hse⟩ := M.spec _ _ hacc hacc
    rw [← hs] at hsb hse
    have hinv1 := chain_mul hinv hinv hse
    have hx1 : bv (h1 x) V1 = bv x V := by
      show (h1 x).lookup V1 = x.lookup V
      rw [Var.lookup_rename, hV1]
    cases b with
    | true =>
      refine mulK_denote M Q (h1 x) s _ V1 fun h2 m V2 hV2 hm => ?_
      rw [hx1] at hm
      obtain ⟨hmb, hme⟩ := M.spec (bv x V) (bv s V1) hx hsb
      rw [← hm] at hme hmb
      have hx0 : ((bv x V).toNat : ZMod p) * M.κ ^ 0 = ((bv x V).toNat : ZMod p) ^ (0 + 1) := by
        ring
      have hinv2 := chain_mul hx0 hinv1 hme
      have hx2 : bv (h2 (h1 x)) V2 = bv x V := by
        show (h2 (h1 x)).lookup V2 = x.lookup V
        rw [Var.lookup_rename, hV2]
        exact hx1
      refine powK_denote Q bs (h2 (h1 x)) m _ V2 (2 * n + 2) (hx2 ▸ hx) hmb
        (by rw [hx2]; convert hinv2 using 2 <;> ring) ?_
      intro Γ3 h3 v V3 hV3 hvb hve
      refine hk _ v V3 ?_ hvb (by rw [← hx2]; exact hve)
      show pullV (fun u => h3 (h2 (h1 u))) V3 = V
      rw [pullV_comp, pullV_comp, hV3, hV2, hV1]
    | false =>
      refine powK_denote Q bs (h1 x) s _ V1 (2 * n + 1) (hx1 ▸ hx) (hs ▸ hsb)
        (by rw [hx1]; convert hinv1 using 2 <;> ring) ?_
      intro Γ3 h3 v V3 hV3 hvb hve
      refine hk _ v V3 ?_ hvb (by rw [← hx1]; exact hve)
      show pullV (fun u => h3 (h1 u)) V3 = V
      rw [pullV_comp, hV3, hV1]

/-- The one-input context. -/
abbrev C1 (w : ℕ) : JCtxt := [Rw w]

/-- The S-box program: the schedule of the digits `bits` on its input. -/
def sboxProg (bits : List Bool) : Com jasminDialect (C1 w) (Rw w) :=
  powK M bits .here .here fun _ v => .ret v

/-- **The S-box.** On an input at most the chain bound, the output `z` is at most the
chain bound and satisfies `z · κ ^ (d − 1) = x ^ d` for `d = nexp bits 0 + 1`. -/
theorem sboxProg_spec (bits : List Bool) (x : BitVec w) (hx : x.toNat ≤ M.bound) :
    ((sboxProg M bits).denote (.cons x .nil) : BitVec w).toNat ≤ M.bound ∧
      (((sboxProg M bits).denote (.cons x .nil) : BitVec w).toNat : ZMod p)
          * M.κ ^ nexp bits 0 = (x.toNat : ZMod p) ^ (nexp bits 0 + 1) := by
  refine powK_denote M (fun z : BitVec w => z.toNat ≤ M.bound ∧
      (z.toNat : ZMod p) * M.κ ^ nexp bits 0 = (x.toNat : ZMod p) ^ (nexp bits 0 + 1))
    bits (.here : Var (C1 w) (Rw w)) .here (fun _ v => .ret v) (.cons x .nil) 0 hx hx
    (by simp) ?_
  intro Γ' h v V' _ hvb hve
  exact ⟨hvb, hve⟩

end Sbox

/-- **The S-box against `sbox`.** When `κ` is a unit and the input word represents `u` as
`u · κ`, the output word represents `sbox P u` as `sbox P u · κ`, with the chain bound. -/
theorem sboxProg_sbox {w : ℕ} (P : Params) (M : ChainMul w P.p) (bits : List Bool)
    (hd : nexp bits 0 + 1 = P.sboxDeg) {κ' : ZMod P.p} (hκ : M.κ * κ' = 1) (x : BitVec w)
    (hx : x.toNat ≤ M.bound) {u : ZMod P.p} (hu : (x.toNat : ZMod P.p) = u * M.κ) :
    ((sboxProg M bits).denote (.cons x .nil) : BitVec w).toNat ≤ M.bound ∧
      (((sboxProg M bits).denote (.cons x .nil) : BitVec w).toNat : ZMod P.p)
        = sbox P u * M.κ := by
  obtain ⟨hb, e⟩ := sboxProg_spec M bits x hx
  refine ⟨hb, ?_⟩
  set z : ZMod P.p := (((sboxProg M bits).denote (.cons x .nil) : BitVec w).toNat : ZMod P.p)
  set n := nexp bits 0
  rw [hu] at e
  unfold sbox
  rw [← hd]
  calc z = z * (M.κ * κ') ^ n := by rw [hκ, one_pow, mul_one]
    _ = (z * M.κ ^ n) * κ' ^ n := by ring
    _ = u ^ (n + 1) * M.κ * (M.κ * κ') ^ n := by rw [e]; ring
    _ = u ^ (n + 1) * M.κ := by rw [hκ, one_pow, mul_one]

/-! ## 3. The linear-layer blocks -/

/-- The accumulator lane, `2 w` bits. -/
abbrev Rd (w : ℕ) : JasminTy := Rw (2 * w)

/-- The context after a row. -/
abbrev X9 (w : ℕ) (Γ : JCtxt) : JCtxt :=
  Rd w :: Rd w :: Rd w :: Rd w :: Rd w :: Rd w :: Rd w :: Rd w :: Rd w :: Γ

/-- A variable seen past a row. -/
def up9 {w : ℕ} {Γ : JCtxt} {t : JasminTy} (v : Var Γ t) : Var (X9 w Γ) t :=
  .there (.there (.there (.there (.there (.there (.there (.there (.there v))))))))

/-- The row `2 a + 3 b + c + d` of `circ(2, 3, 1, 1)` at `2 w` bits, then `k` with the row
at `.here`: `s = a + b`, `((s + s) + b) + c + d`. -/
def rowK {w : ℕ} {Γ : JCtxt} {t : JasminTy} (a b c d : Var Γ (Rw w))
    (k : Com jasminDialect (X9 w Γ) t) : Com jasminDialect Γ t :=
  .var (castE w (2 * w) a) <|
  .var (castE w (2 * w) (.there b)) <|
  .var (castE w (2 * w) (.there (.there c))) <|
  .var (castE w (2 * w) (.there (.there (.there d)))) <|
  .var (binE .add (2 * w) (.there (.there (.there .here))) (.there (.there .here))) <|
  .var (binE .add (2 * w) .here .here) <|
  .var (binE .add (2 * w) .here (.there (.there (.there (.there .here))))) <|
  .var (binE .add (2 * w) .here (.there (.there (.there (.there .here))))) <|
  .var (binE .add (2 * w) .here (.there (.there (.there (.there .here))))) k

/-- The context after a reduction. -/
abbrev X8 (w : ℕ) (Γ : JCtxt) : JCtxt :=
  Rw w :: Rd w :: Rd w :: Rd w :: Rd w :: Rd w :: Rd w :: Rd w :: Γ

/-- The Barrett reduction of the `2 w`-bit variable `a` modulo `p` to `w` bits,
`a − ⌊⌊a / 2 ^ s⌋ · m / 2 ^ k⌋ · p`, then `kk` with the result at `.here`. -/
def redK {w : ℕ} {Γ : JCtxt} {t : JasminTy} (p s k m : ℕ) (a : Var Γ (Rd w))
    (kk : Com jasminDialect (X8 w Γ) t) : Com jasminDialect Γ t :=
  .var (shrE (2 * w) s a) <|
  .var (constE (2 * w) m) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (shrE (2 * w) k .here) <|
  .var (constE (2 * w) p) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  .var (binE .sub (2 * w)
    (.there (.there (.there (.there (.there (.there a)))))) .here) <|
  .var (castE (2 * w) w .here) kk

/-- The integer semantics of a row. -/
def rowZ (a b c d : ℤ) : ℤ := a + b + (a + b) + b + c + d

/-- The integer semantics of the reduction. -/
def redZ (w p s k m : ℕ) (a : ℤ) : ℤ := a - a / 2 ^ s * cW (2 * w) m / 2 ^ k * cW (2 * w) p

theorem redZ_cast (w p s k m : ℕ) (hp : p < 2 ^ (2 * w)) (a : ℤ) :
    ((redZ w p s k m a : ℤ) : ZMod p) = a := by
  unfold redZ
  rw [cW_of_lt hp]
  push_cast
  simp

/-- The integer values after `rowK a b c d`. -/
def rowZV {w : ℕ} {Γ : JCtxt} (a b c d : Var Γ (Rw w)) (Z : ZVec Γ) : ZVec (X9 w Γ) :=
  let A := hget Z a
  let B := hget Z b
  let C := hget Z c
  let D := hget Z d
  .cons (A + B + (A + B) + B + C + D) (.cons (A + B + (A + B) + B + C)
    (.cons (A + B + (A + B) + B) (.cons (A + B + (A + B)) (.cons (A + B)
      (.cons D (.cons C (.cons B (.cons A Z))))))))

theorem rowK_denoteZ {w : ℕ} {Γ : JCtxt} {t : JasminTy} (a b c d : Var Γ (Rw w))
    (k : Com jasminDialect (X9 w Γ) t) (Z : ZVec Γ) :
    (rowK a b c d k).denoteZ Z = k.denoteZ (rowZV a b c d Z) := rfl

theorem hget_rowZV_up9 {w : ℕ} {Γ : JCtxt} {t : JasminTy} (a b c d : Var Γ (Rw w))
    (Z : ZVec Γ) (v : Var Γ t) : hget (rowZV a b c d Z) (up9 v) = hget Z v := rfl

theorem redK_ret_denoteZ {w : ℕ} {Γ : JCtxt} (p s k m : ℕ) (a : Var Γ (Rd w)) (Z : ZVec Γ) :
    (redK p s k m a (.ret .here)).denoteZ Z = redZ w p s k m (hget Z a) := rfl

/-- The reading of lane `j` of `n + 1` lanes. -/
theorem hget_lane {w : ℕ} (g : ℕ → BitVec w) {n j : ℕ} (hj : j ≤ n) :
    hget (zvals false (lanesVal (Rw w) g (n + 1) 0)) (laneVarG (Rw w) n j)
      = ((g j).toNat : ℤ) := by
  rw [hget_zvals]
  have := laneVarG_lookup (Rw w) g n j 0 hj
  rw [Nat.zero_add] at this
  simp only [rdT, rd, Bool.false_eq_true, ite_false]
  rw [this]

/-- Lane `j` of the twenty-lane context. -/
abbrev ln20 (w j : ℕ) : Var (Ctxs w 20) (Rw w) := laneVarG (Rw w) 19 j

/-- The lane block of the external layer on lanes `x₀, …, x₁₉`: the rows
`Y_g = 2 x_{4g} + 3 x_{4g+1} + x_{4g+2} + x_{4g+3}` for `g = 0, …, 4`, then the reduction
of `Y₄ + (Y₀ + Y₁ + Y₂ + Y₃)`. Lanes `16, …, 19` repeat the group of the output lane. -/
def extBlk (w p s k m : ℕ) : Com jasminDialect (Ctxs w 20) (Rw w) :=
  rowK (ln20 w 0) (ln20 w 1) (ln20 w 2) (ln20 w 3) <|
  rowK (up9 (ln20 w 4)) (up9 (ln20 w 5)) (up9 (ln20 w 6)) (up9 (ln20 w 7)) <|
  rowK (up9 (up9 (ln20 w 8))) (up9 (up9 (ln20 w 9))) (up9 (up9 (ln20 w 10)))
    (up9 (up9 (ln20 w 11))) <|
  rowK (up9 (up9 (up9 (ln20 w 12)))) (up9 (up9 (up9 (ln20 w 13))))
    (up9 (up9 (up9 (ln20 w 14)))) (up9 (up9 (up9 (ln20 w 15)))) <|
  rowK (up9 (up9 (up9 (up9 (ln20 w 16))))) (up9 (up9 (up9 (up9 (ln20 w 17)))))
    (up9 (up9 (up9 (up9 (ln20 w 18))))) (up9 (up9 (up9 (up9 (ln20 w 19))))) <|
  .var (binE .add (2 * w) (up9 (up9 (up9 (up9 .here)))) (up9 (up9 (up9 .here)))) <|
  .var (binE .add (2 * w) .here (.there (up9 (up9 .here)))) <|
  .var (binE .add (2 * w) .here (.there (.there (up9 .here)))) <|
  .var (binE .add (2 * w) (.there (.there (.there .here))) .here) <|
  redK p s k m .here <|
  .ret .here

/-- The integer semantics of `extBlk` on the lane values `z`. -/
def extZ (w p s k m : ℕ) (z : ℕ → ℤ) : ℤ :=
  let Y := fun g => rowZ (z (4 * g)) (z (4 * g + 1)) (z (4 * g + 2)) (z (4 * g + 3))
  redZ w p s k m (Y 4 + (Y 0 + Y 1 + Y 2 + Y 3))

theorem extBlk_denoteZ (w p s k m : ℕ) (g : ℕ → BitVec w) :
    (extBlk w p s k m).denoteZ (zvals false (lanesVal (Rw w) g 20 0))
      = extZ w p s k m (fun j => ((g j).toNat : ℤ)) := by
  rw [extBlk, rowK_denoteZ, rowK_denoteZ, rowK_denoteZ, rowK_denoteZ, rowK_denoteZ]
  simp (disch := omega) only [rowZV, up9, hget, hget_lane]
  rfl

/-- The sum of the lanes `lane 0, …, lane (n − 1)` added to `acc` at `2 w` bits, then
`fin` at the sum. -/
def sumK {w : ℕ} {t : JasminTy} : (n : ℕ) → {Γ : JCtxt} → (ℕ → Var Γ (Rw w)) →
    Var Γ (Rd w) → (∀ {Γ' : JCtxt}, Var Γ' (Rd w) → Com jasminDialect Γ' t) →
    Com jasminDialect Γ t
  | 0, _, _, acc, fin => fin acc
  | n + 1, _, lane, acc, fin =>
    .var (castE w (2 * w) (lane 0)) <|
    .var (binE .add (2 * w) (.there acc) .here) <|
    sumK n (fun j => .there (.there (lane (j + 1)))) .here fin

/-- `a + f 0 + ⋯ + f (n − 1)`, added from the left. -/
def foldSum : ℕ → ℤ → (ℕ → ℤ) → ℤ
  | 0, a, _ => a
  | n + 1, a, f => foldSum n (a + f 0) fun j => f (j + 1)

theorem sumK_red_denoteZ {w : ℕ} (p s k m : ℕ) : ∀ (n : ℕ) {Γ : JCtxt}
    (lane : ℕ → Var Γ (Rw w)) (acc : Var Γ (Rd w)) (Z : ZVec Γ),
    (sumK n lane acc fun v => redK p s k m v (.ret .here)).denoteZ Z
      = redZ w p s k m (foldSum n (hget Z acc) fun j => hget Z (lane j))
  | 0, _, _, _, _ => rfl
  | n + 1, _, lane, _, _ =>
    sumK_red_denoteZ p s k m n (fun j => .there (.there (lane (j + 1)))) .here _

/-- The lane block of the internal layer on `d`, `x` and lanes `x₀, …, x₁₅`: the reduction
of `d · x + x₀ + ⋯ + x₁₅`. -/
def intBlk (w p s k m : ℕ) : Com jasminDialect (Rw w :: Rw w :: Ctxs w 16) (Rw w) :=
  .var (castE w (2 * w) .here) <|
  .var (castE w (2 * w) (.there (.there .here))) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  sumK 16 (fun j => .there (.there (.there (.there (.there (ln w j)))))) .here
    fun v => redK p s k m v (.ret .here)

/-- The sum of `z 0, …, z 15`, added from the left. -/
def sum16Z (z : ℕ → ℤ) : ℤ :=
  z 0 + z 1 + z 2 + z 3 + z 4 + z 5 + z 6 + z 7 + z 8 + z 9 + z 10 + z 11 + z 12 + z 13 +
    z 14 + z 15

theorem foldSum_sixteen (a : ℤ) (z : ℕ → ℤ) : foldSum 16 a z = sum16Z z + a := by
  simp only [foldSum, sum16Z]
  ring

/-- The integer semantics of `intBlk`. -/
def intZ (w p s k m : ℕ) (d x : ℤ) (z : ℕ → ℤ) : ℤ := redZ w p s k m (sum16Z z + d * x)

theorem intBlk_denoteZ (w p s k m : ℕ) (d x : BitVec w) (g : ℕ → BitVec w) :
    (intBlk w p s k m).denoteZ (zvals false (.cons d (.cons x (lanesVal (Rw w) g 16 0))))
      = intZ w p s k m d.toNat x.toNat (fun j => ((g j).toNat : ℤ)) := by
  rw [intBlk, Com.denoteZ, Com.denoteZ, Com.denoteZ, sumK_red_denoteZ, foldSum_sixteen, intZ]
  congr 2

/-! ## 4. Side conditions and the block theorems -/

/-- The parameters of the linear layers modulo `p`: the input bound of a lane, and for each
layer the Barrett shifts, the Barrett multiplier and the output bound. -/
structure LinRed where
  /-- Every input lane is at most `inB`. -/
  inB : ℕ
  /-- The first Barrett shift of the external layer. -/
  extS : ℕ
  /-- The second Barrett shift of the external layer. -/
  extK : ℕ
  /-- The Barrett multiplier of the external layer. -/
  extM : ℕ
  /-- The bound of an external output lane. -/
  extOut : ℕ
  /-- The first Barrett shift of the internal layer. -/
  intS : ℕ
  /-- The second Barrett shift of the internal layer. -/
  intK : ℕ
  /-- The Barrett multiplier of the internal layer. -/
  intM : ℕ
  /-- The bound of an internal output lane. -/
  intOut : ℕ

/-- The side condition of the external layer: `p` fits `2 w` bits, and the bounds check of
`extBlk` from lanes in `[0, inB]` to `[0, extOut]`. -/
def LinRed.extOk (w p : ℕ) (L : LinRed) : Bool :=
  decide (p < 2 ^ (2 * w)) &&
    boundsOk false (hvConst (0, L.inB) (Ctxs w 20)) (extBlk w p L.extS L.extK L.extM)
      (0, L.extOut)

/-- The input intervals of `intBlk`: the diagonal constant in `[0, p − 1]`, the lanes in
`[0, inB]`. -/
def intIvs (w p inB : ℕ) : HVector (fun _ => Iv) (Rw w :: Rw w :: Ctxs w 16) :=
  .cons (0, ((p - 1 : ℕ) : ℤ)) (.cons (0, inB) (hvConst (0, inB) (Ctxs w 16)))

/-- The side condition of the internal layer: `p` fits `2 w` bits and is at most `2 ^ w`,
and the bounds check of `intBlk` from `intIvs` to `[0, intOut]`. -/
def LinRed.intOk (w p : ℕ) (L : LinRed) : Bool :=
  decide (p < 2 ^ (2 * w) ∧ p ≤ 2 ^ w) &&
    boundsOk false (intIvs w p L.inB) (intBlk w p L.intS L.intK L.intM) (0, L.intOut)

theorem valsIn_lanes {w B n : ℕ} (g : ℕ → BitVec w) (hg : ∀ j < n, (g j).toNat ≤ B) :
    ValsIn false (hvConst (0, (B : ℤ)) (Ctxs w n)) (lanesVal (Rw w) g n 0) := by
  refine (valsIn_const false w (0, (B : ℤ)) n _).mpr fun j hj => ?_
  rw [NegacyclicNttTemplate.hvGetG_lanesVal (Rw w) (0 : BitVec w) g n 0 j hj, Nat.zero_add]
  simp only [rd, Bool.false_eq_true, ite_false]
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast hg j hj⟩

/-- On lanes at most `inB`, the output of `extBlk` is its integer semantics and is at most
`extOut`. -/
theorem extBlk_word {w p : ℕ} (L : LinRed) (h : L.extOk w p = true) (g : ℕ → BitVec w)
    (hg : ∀ j < 20, (g j).toNat ≤ L.inB) :
    ((((extBlk w p L.extS L.extK L.extM).denote (lanesVal (Rw w) g 20 0) : BitVec w).toNat
        : ℤ)) = extZ w p L.extS L.extK L.extM (fun j => ((g j).toNat : ℤ)) ∧
      ((extBlk w p L.extS L.extK L.extM).denote (lanesVal (Rw w) g 20 0) : BitVec w).toNat
        ≤ L.extOut := by
  simp only [LinRed.extOk, Bool.and_eq_true] at h
  obtain ⟨h1, -, h3⟩ := denote_eq_denoteZ_of_boundsOk false _ _ _ h.2 _ (valsIn_lanes g hg)
  rw [extBlk_denoteZ] at h1
  simp only [rd, Bool.false_eq_true, ite_false] at h1 h3
  exact ⟨h1, by exact_mod_cast h3⟩

/-- On a diagonal constant at most `p − 1` and lanes at most `inB`, the output of `intBlk`
is its integer semantics and is at most `intOut`. -/
theorem intBlk_word {w p : ℕ} (L : LinRed) (h : L.intOk w p = true) (d x : BitVec w)
    (hd : d.toNat ≤ p - 1) (hx : x.toNat ≤ L.inB) (g : ℕ → BitVec w)
    (hg : ∀ j < 16, (g j).toNat ≤ L.inB) :
    ((((intBlk w p L.intS L.intK L.intM).denote (.cons d (.cons x (lanesVal (Rw w) g 16 0)))
        : BitVec w).toNat : ℤ)) = intZ w p L.intS L.intK L.intM d.toNat x.toNat
          (fun j => ((g j).toNat : ℤ)) ∧
      ((intBlk w p L.intS L.intK L.intM).denote (.cons d (.cons x (lanesVal (Rw w) g 16 0)))
        : BitVec w).toNat ≤ L.intOut := by
  simp only [LinRed.intOk, Bool.and_eq_true] at h
  have hV : ValsIn false (intIvs w p L.inB) (.cons d (.cons x (lanesVal (Rw w) g 16 0))) :=
    ⟨⟨by simp [rd], by simp [rd]; omega⟩, ⟨by simp [rd], by simp [rd]; omega⟩,
      valsIn_lanes g hg⟩
  obtain ⟨h1, -, h3⟩ := denote_eq_denoteZ_of_boundsOk false _ _ _ h.2 _ hV
  rw [intBlk_denoteZ] at h1
  simp only [rd, Bool.false_eq_true, ite_false] at h1 h3
  exact ⟨h1, by exact_mod_cast h3⟩

/-! ## 5. The layers on sixteen lanes -/

/-- The input lane that position `j` of `extBlk` reads for output lane `i`: position
`(i + j) mod 4` of group `j / 4` for `j < 16`, and of the group `i / 4` of the output lane
for `j ≥ 16`. -/
def extIdx (i j : ℕ) : ℕ := 4 * (if j < 16 then j / 4 else i / 4) + (i % 4 + j % 4) % 4

theorem extIdx_le (i j : ℕ) (hi : i < 16) : extIdx i j ≤ 15 := by
  unfold extIdx
  split <;> omega

/-- Output lane `i` of the external layer: `extBlk` on the input lanes `extIdx i`. -/
def extLane (w p s k m i : ℕ) : Com jasminDialect (Ctxs w 16) (Rw w) :=
  (extBlk w p s k m).rename (homOf (lanesHV (fun j => ln w (extIdx i j)) 20 0))

/-- The external layer on sixteen lanes. -/
def extProg (w p : ℕ) (L : LinRed) : MultiReturnCom jasminDialect (Ctxs w 16) (Ctxs w 16) :=
  laneMapW 16 (extLane w p L.extS L.extK L.extM)

theorem extLane_denote (w p s k m : ℕ) {i : ℕ} (hi : i < 16) (g : ℕ → BitVec w) :
    (extLane w p s k m i).denote (lanesVal (Rw w) g 16 0)
      = (extBlk w p s k m).denote (lanesVal (Rw w) (fun j => g (extIdx i j)) 20 0) := by
  rw [extLane, Com.denote_rename, pullV_homOf, lookupVars_lanesHV]
  exact congrArg (fun f => (extBlk w p s k m).denote (lanesVal (Rw w) f 20 0))
    (funext fun j => ln_lookup w g (extIdx_le i j hi))

/-- The row `2 a + 3 b + c + d` in the order `extBlk` adds it. -/
def rowF {R : Type} [CommRing R] (a b c d : R) : R := a + b + (a + b) + b + c + d

/-- Lane `n` of the 4×4 block layer is the row of its group, rotated to start at `n`. -/
theorem mdsPre_apply {P : Params} (y : ℕ → ZMod P.p) (n : ℕ) (hn : n < 16) :
    mdsPre (P := P) (fun k : Fin 16 => y k) ⟨n, hn⟩
      = rowF (y (4 * (n / 4) + n % 4)) (y (4 * (n / 4) + (n % 4 + 1) % 4))
          (y (4 * (n / 4) + (n % 4 + 2) % 4)) (y (4 * (n / 4) + (n % 4 + 3) % 4)) := by
  simp only [mdsPre, mat4]
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h <;>
    simp [h, rowF] <;> ring

/-- **The external layer, rearranged.** Lane `i` of `externalMDS` is the row of the group of
`i` plus the rows of the four groups, each rotated to start at position `i mod 4`, read
through `extIdx i`. -/
theorem externalMDS_eq {P : Params} (y : ℕ → ZMod P.p) (i : Fin 16) :
    externalMDS (P := P) (fun k : Fin 16 => y k) i
      = rowF (y (extIdx i 16)) (y (extIdx i 17)) (y (extIdx i 18)) (y (extIdx i 19)) +
        (rowF (y (extIdx i 0)) (y (extIdx i 1)) (y (extIdx i 2)) (y (extIdx i 3)) +
          rowF (y (extIdx i 4)) (y (extIdx i 5)) (y (extIdx i 6)) (y (extIdx i 7)) +
          rowF (y (extIdx i 8)) (y (extIdx i 9)) (y (extIdx i 10)) (y (extIdx i 11)) +
          rowF (y (extIdx i 12)) (y (extIdx i 13)) (y (extIdx i 14)) (y (extIdx i 15))) := by
  obtain ⟨n, hn⟩ := i
  simp only [externalMDS, colSumMap]
  rw [mdsPre_apply, mdsPre_apply, mdsPre_apply, mdsPre_apply, mdsPre_apply]
  have e0 : n % 4 / 4 = 0 := by omega
  have e1 : (n % 4 + 4) / 4 = 1 := by omega
  have e2 : (n % 4 + 8) / 4 = 2 := by omega
  have e3 : (n % 4 + 12) / 4 = 3 := by omega
  have f1 : (n % 4 + 4) % 4 = n % 4 := by omega
  have f2 : (n % 4 + 8) % 4 = n % 4 := by omega
  have f3 : (n % 4 + 12) % 4 = n % 4 := by omega
  simp only [extIdx, e0, e1, e2, e3, f1, f2, f3, Nat.mod_mod]
  norm_num

/-- **The external layer.** On input lanes at most `inB`, every output lane of `extProg` is
at most `extOut` and is the lane of `externalMDS` of the inputs modulo `p`. -/
theorem extProg_spec {w : ℕ} (P : Params) (L : LinRed) (h : L.extOk w P.p = true)
    (g : ℕ → BitVec w) (hg : ∀ j < 16, (g j).toNat ≤ L.inB) (i : Fin 16) :
    (hvGetG (Rw w) (0 : BitVec w) ((extProg w P.p L).denote (lanesVal (Rw w) g 16 0)) i).toNat
        ≤ L.extOut ∧
      ((hvGetG (Rw w) (0 : BitVec w) ((extProg w P.p L).denote (lanesVal (Rw w) g 16 0))
        i).toNat : ZMod P.p) = externalMDS (P := P) (fun j => ((g j).toNat : ZMod P.p)) i := by
  rw [extProg, laneMapW_denote, hvGetG_denoteN (Rw w) (0 : BitVec w) 16 _ _ i i.isLt,
    extLane_denote _ _ _ _ _ i.isLt]
  obtain ⟨e, hb⟩ := extBlk_word L h (fun j => g (extIdx i j))
    (fun j _ => hg _ (Nat.lt_succ_of_le (extIdx_le i j i.isLt)))
  refine ⟨hb, ?_⟩
  have hp : P.p < 2 ^ (2 * w) := by
    simp only [LinRed.extOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  rw [← Int.cast_natCast, e, extZ, redZ_cast w P.p _ _ _ hp,
    externalMDS_eq (fun j => ((g j).toNat : ZMod P.p))]
  push_cast [rowZ, rowF]
  rfl

/-- Output lane `i` of the internal layer: `intBlk` on the diagonal constant `dg i`, lane
`i` and the sixteen lanes. -/
def intLane (w p s k m : ℕ) (dg : ℕ → ℕ) (i : ℕ) : Com jasminDialect (Ctxs w 16) (Rw w) :=
  .var (constE w (dg i)) ((intBlk w p s k m).rename
    (homOf (.cons .here (.cons (.there (ln w i)) (lanesHV (fun j => .there (ln w j)) 16 0)))))

/-- The internal layer on sixteen lanes, with diagonal constants `dg`. -/
def intProg (w p : ℕ) (L : LinRed) (dg : ℕ → ℕ) :
    MultiReturnCom jasminDialect (Ctxs w 16) (Ctxs w 16) :=
  laneMapW 16 (intLane w p L.intS L.intK L.intM dg)

theorem lanesVal_congr {w : ℕ} {f f' : ℕ → BitVec w} :
    ∀ (n off : ℕ), (∀ j, off ≤ j → j < off + n → f j = f' j) →
      lanesVal (Rw w) f n off = lanesVal (Rw w) f' n off
  | 0, _, _ => rfl
  | n + 1, off, h => by
    show HVector.cons _ _ = HVector.cons _ _
    rw [h off le_rfl (by omega), lanesVal_congr n (off + 1) fun j h1 h2 => h j (by omega) (by omega)]

theorem intLane_denote (w p s k m : ℕ) (dg : ℕ → ℕ) {i : ℕ} (hi : i ≤ 15)
    (g : ℕ → BitVec w) :
    (intLane w p s k m dg i).denote (lanesVal (Rw w) g 16 0)
      = (intBlk w p s k m).denote
          (.cons (BitVec.ofNat w (dg i)) (.cons (g i) (lanesVal (Rw w) g 16 0))) := by
  rw [intLane, Com.denote, Com.denote_rename, pullV_homOf]
  show (intBlk w p s k m).denote (.cons _ (.cons _ (MultiReturnCom.lookupVars _ _))) = _
  rw [lookupVars_lanesHV]
  congr 2
  exact congrArg₂ HVector.cons (ln_lookup w g hi)
    (lanesVal_congr 16 0 fun j _ hj => ln_lookup w g (by omega))

/-- The diagonal of `P` as canonical residues, `0` past lane 15. -/
def diagNat (P : Params) (i : ℕ) : ℕ := if h : i < 16 then (P.diag ⟨i, h⟩).val else 0

theorem diagNat_spec (P : Params) [NeZero P.p] (i : Fin 16) :
    diagNat P i < P.p ∧ ((diagNat P i : ℕ) : ZMod P.p) = P.diag i := by
  simp [diagNat, ZMod.val_lt]

/-- **The internal layer.** With diagonal constants `dg` that are residues below `p` of the
diagonal of `P`, on input lanes at most `inB`, every output lane of `intProg` is at most
`intOut` and is the lane of `internalMDS P` of the inputs modulo `p`. -/
theorem intProg_spec {w : ℕ} (P : Params) (L : LinRed) (h : L.intOk w P.p = true)
    (dg : ℕ → ℕ) (hdg : ∀ i : Fin 16, dg i < P.p ∧ ((dg i : ℕ) : ZMod P.p) = P.diag i)
    (g : ℕ → BitVec w) (hg : ∀ j < 16, (g j).toNat ≤ L.inB) (i : Fin 16) :
    (hvGetG (Rw w) (0 : BitVec w) ((intProg w P.p L dg).denote (lanesVal (Rw w) g 16 0))
        i).toNat ≤ L.intOut ∧
      ((hvGetG (Rw w) (0 : BitVec w) ((intProg w P.p L dg).denote (lanesVal (Rw w) g 16 0))
        i).toNat : ZMod P.p) = internalMDS P (fun j => ((g j).toNat : ZMod P.p)) i := by
  have hi : i.val ≤ 15 := Nat.le_of_lt_succ i.isLt
  have hpw : P.p < 2 ^ (2 * w) ∧ P.p ≤ 2 ^ w := by
    simp only [LinRed.intOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have hd : (BitVec.ofNat w (dg i)).toNat = dg i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le (hdg i).1 hpw.2)]
  rw [intProg, laneMapW_denote, hvGetG_denoteN (Rw w) (0 : BitVec w) 16 _ _ i i.isLt,
    intLane_denote w P.p _ _ _ dg hi]
  obtain ⟨e, hb⟩ := intBlk_word L h (BitVec.ofNat w (dg i)) (g i)
    (by rw [hd]; have := (hdg i).1; omega) (hg i i.isLt) g hg
  refine ⟨hb, ?_⟩
  rw [← Int.cast_natCast, e, intZ, redZ_cast w P.p _ _ _ hpw.1, hd]
  push_cast [sum16Z]
  rw [(hdg i).2]
  simp only [internalMDS, sumAll]
  rfl

/-! ## 6. Instances -/

/-- BabyBear, `p = 2 ^ 31 − 2 ^ 27 + 1`, lanes at most `p`. -/
def bbLin : LinRed :=
  ⟨2013265921, 4, 58, 2290649223, 2013265949, 29, 33, 2290649223, 3250061320⟩

/-- KoalaBear, `p = 2 ^ 31 − 2 ^ 24 + 1`, lanes at most `p`. -/
def kbLin : LinRed :=
  ⟨2130706433, 4, 58, 2164392967, 2130706450, 29, 33, 2164392967, 2766543874⟩

theorem bbLin_extOk : bbLin.extOk 32 2013265921 = true := by decide +kernel
theorem bbLin_intOk : bbLin.intOk 32 2013265921 = true := by decide +kernel
theorem kbLin_extOk : kbLin.extOk 32 2130706433 = true := by decide +kernel
theorem kbLin_intOk : kbLin.intOk 32 2130706433 = true := by decide +kernel

/-- The Mersenne fold block as a chainable multiply, `κ = 1`. -/
def foldChain {w k B : ℕ} (h : foldOk w k B B = true) : ChainMul w (2 ^ k - 1) where
  blk := foldBlk w k
  bound := B
  κ := 1
  spec x y hx hy := by
    have hr := mulFold_rep h (x := x) (y := y) (u := x.toNat) (v := y.toNat)
      ⟨hx, rfl⟩ ⟨hy, rfl⟩
    exact ⟨hr.1, by rw [mul_one]; exact hr.2⟩

/-- The S-box chain at BabyBear: Plantard multiplies on inputs at most `p`. -/
def bbSboxChain : ChainMul 32 2013265921 :=
  plantChain babyBearFieldP babyBearFieldP_plantOk (by decide)

/-- The S-box chain at KoalaBear: Plantard multiplies on inputs at most `p`. -/
def kbSboxChain : ChainMul 32 2130706433 :=
  plantChain koalaBearFieldP koalaBearFieldP_plantOk (by decide)

/-- The S-box chain at Mersenne-31: fold multiplies on inputs at most `2 ^ 31`. -/
def m31SboxChain : ChainMul 32 (2 ^ 31 - 1) := foldChain mersenne31_foldOk

/-- **The BabyBear S-box, degree 7.** On an input at most `p` the output `z` is at most `p`
and `z · (−2 ^ 64) ^ 6 = x ^ 7` modulo `p`. -/
theorem bbSbox_spec (x : BitVec 32) (hx : x.toNat ≤ 2013265921) :
    ((sboxProg bbSboxChain [true, true]).denote (.cons x .nil) : BitVec 32).toNat
        ≤ 2013265921 ∧
      (((sboxProg bbSboxChain [true, true]).denote (.cons x .nil) : BitVec 32).toNat
          : ZMod 2013265921) * (-2 ^ 64) ^ 6 = (x.toNat : ZMod 2013265921) ^ 7 :=
  sboxProg_spec bbSboxChain [true, true] x hx

/-- **The KoalaBear S-box, degree 3.** On an input at most `p` the output `z` is at most
`p` and `z · (−2 ^ 64) ^ 2 = x ^ 3` modulo `p`. -/
theorem kbSbox_spec (x : BitVec 32) (hx : x.toNat ≤ 2130706433) :
    ((sboxProg kbSboxChain [true]).denote (.cons x .nil) : BitVec 32).toNat ≤ 2130706433 ∧
      (((sboxProg kbSboxChain [true]).denote (.cons x .nil) : BitVec 32).toNat
          : ZMod 2130706433) * (-2 ^ 64) ^ 2 = (x.toNat : ZMod 2130706433) ^ 3 :=
  sboxProg_spec kbSboxChain [true] x hx

/-! ## 7. The linear-layer blocks with a folded constant -/

/-- Lane `j` of the twenty lanes behind one constant input. -/
abbrev lc20 (w j : ℕ) : Var (Rw w :: Ctxs w 20) (Rw w) := .there (ln20 w j)

/-- The lane block of the external layer with a folded constant, on the constant `c` and
lanes `x₀, …, x₁₉`: the rows of `extBlk`, then the reduction of
`Y₄ + (Y₀ + Y₁ + Y₂ + Y₃) + c`. -/
def extRcBlk (w p s k m : ℕ) : Com jasminDialect (Rw w :: Ctxs w 20) (Rw w) :=
  rowK (lc20 w 0) (lc20 w 1) (lc20 w 2) (lc20 w 3) <|
  rowK (up9 (lc20 w 4)) (up9 (lc20 w 5)) (up9 (lc20 w 6)) (up9 (lc20 w 7)) <|
  rowK (up9 (up9 (lc20 w 8))) (up9 (up9 (lc20 w 9))) (up9 (up9 (lc20 w 10)))
    (up9 (up9 (lc20 w 11))) <|
  rowK (up9 (up9 (up9 (lc20 w 12)))) (up9 (up9 (up9 (lc20 w 13))))
    (up9 (up9 (up9 (lc20 w 14)))) (up9 (up9 (up9 (lc20 w 15)))) <|
  rowK (up9 (up9 (up9 (up9 (lc20 w 16))))) (up9 (up9 (up9 (up9 (lc20 w 17)))))
    (up9 (up9 (up9 (up9 (lc20 w 18))))) (up9 (up9 (up9 (up9 (lc20 w 19))))) <|
  .var (binE .add (2 * w) (up9 (up9 (up9 (up9 .here)))) (up9 (up9 (up9 .here)))) <|
  .var (binE .add (2 * w) .here (.there (up9 (up9 .here)))) <|
  .var (binE .add (2 * w) .here (.there (.there (up9 .here)))) <|
  .var (binE .add (2 * w) (.there (.there (.there .here))) .here) <|
  .var (castE w (2 * w) (.there (.there (.there (.there
    (up9 (up9 (up9 (up9 (up9 (.here : Var (Rw w :: Ctxs w 20) (Rw w)))))))))))) <|
  .var (binE .add (2 * w) (.there .here) .here) <|
  redK p s k m .here <|
  .ret .here

/-- The integer semantics of `extRcBlk` on the constant `c` and the lane values `z`. -/
def extRcZ (w p s k m : ℕ) (c : ℤ) (z : ℕ → ℤ) : ℤ :=
  let Y := fun g => rowZ (z (4 * g)) (z (4 * g + 1)) (z (4 * g + 2)) (z (4 * g + 3))
  redZ w p s k m (Y 4 + (Y 0 + Y 1 + Y 2 + Y 3) + c)

theorem extRcBlk_denoteZ (w p s k m : ℕ) (c : BitVec w) (g : ℕ → BitVec w) :
    (extRcBlk w p s k m).denoteZ (zvals false (.cons c (lanesVal (Rw w) g 20 0)))
      = extRcZ w p s k m c.toNat (fun j => ((g j).toNat : ℤ)) := by
  rw [extRcBlk, rowK_denoteZ, rowK_denoteZ, rowK_denoteZ, rowK_denoteZ, rowK_denoteZ]
  simp only [rowZV, up9, hget]
  rfl

/-- The lane block of the internal layer with a folded constant, on the constant `c`, the
diagonal constant `d`, the lane `x` and lanes `x₀, …, x₁₅`: the reduction `r` of `d · x`,
then the reduction of `x₀ + ⋯ + x₁₅ + (r + c)`. -/
def intRcBlk (w p s₁ k₁ m₁ s k m : ℕ) :
    Com jasminDialect (Rw w :: Rw w :: Rw w :: Ctxs w 16) (Rw w) :=
  .var (castE w (2 * w) (.there .here)) <|
  .var (castE w (2 * w) (.there (.there (.there .here)))) <|
  .var (binE .mul (2 * w) (.there .here) .here) <|
  redK p s₁ k₁ m₁ .here <|
  .var (castE w (2 * w) .here) <|
  .var (castE w (2 * w) (.there (.there (.there (.there (.there (.there (.there (.there
    (.there (.there (.there (.there .here))))))))))))) <|
  .var (binE .add (2 * w) (.there .here) .here) <|
  sumK 16 (fun j => .there (.there (.there (.there (.there (.there (.there (.there (.there
    (.there (.there (.there (.there (.there (.there (.there (.there (ln w j))))))))))))))))))
    .here fun v => redK p s k m v (.ret .here)

/-- The integer semantics of `intRcBlk`. -/
def intRcZ (w p s₁ k₁ m₁ s k m : ℕ) (c d x : ℤ) (z : ℕ → ℤ) : ℤ :=
  redZ w p s k m (sum16Z z + (redZ w p s₁ k₁ m₁ (d * x) + c))

theorem intRcBlk_denoteZ (w p s₁ k₁ m₁ s k m : ℕ) (c d x : BitVec w) (g : ℕ → BitVec w) :
    (intRcBlk w p s₁ k₁ m₁ s k m).denoteZ
        (zvals false (.cons c (.cons d (.cons x (lanesVal (Rw w) g 16 0)))))
      = intRcZ w p s₁ k₁ m₁ s k m c.toNat d.toNat x.toNat (fun j => ((g j).toNat : ℤ)) := by
  rw [intRcBlk, Com.denoteZ, Com.denoteZ, Com.denoteZ, redK]
  simp only [Com.denoteZ]
  rw [sumK_red_denoteZ, foldSum_sixteen, intRcZ]
  simp only [hget]
  rfl

/-- The parameters of the linear layers with folded constants modulo `p`: the input bound
of a lane, the Barrett constants and output bound of the external layer, the Barrett
constants of the diagonal product, and the Barrett constants and output bound of the
internal layer. -/
structure RcRed where
  /-- Every input lane is at most `inB`. -/
  inB : ℕ
  /-- The first Barrett shift of the external layer. -/
  extS : ℕ
  /-- The second Barrett shift of the external layer. -/
  extK : ℕ
  /-- The Barrett multiplier of the external layer. -/
  extM : ℕ
  /-- The bound of an external output lane. -/
  extOut : ℕ
  /-- The first Barrett shift of the diagonal product. -/
  mulS : ℕ
  /-- The second Barrett shift of the diagonal product. -/
  mulK : ℕ
  /-- The Barrett multiplier of the diagonal product. -/
  mulM : ℕ
  /-- The first Barrett shift of the internal layer. -/
  intS : ℕ
  /-- The second Barrett shift of the internal layer. -/
  intK : ℕ
  /-- The Barrett multiplier of the internal layer. -/
  intM : ℕ
  /-- The bound of an internal output lane. -/
  intOut : ℕ

/-- The input intervals of `extRcBlk`: the constant in `[0, p − 1]`, the lanes in
`[0, inB]`. -/
def extRcIvs (w p inB : ℕ) : HVector (fun _ => Iv) (Rw w :: Ctxs w 20) :=
  .cons (0, ((p - 1 : ℕ) : ℤ)) (hvConst (0, inB) (Ctxs w 20))

/-- The input intervals of `intRcBlk`: the constant and the diagonal constant in
`[0, p − 1]`, the lanes in `[0, inB]`. -/
def intRcIvs (w p inB : ℕ) : HVector (fun _ => Iv) (Rw w :: Rw w :: Rw w :: Ctxs w 16) :=
  .cons (0, ((p - 1 : ℕ) : ℤ)) (.cons (0, ((p - 1 : ℕ) : ℤ)) (.cons (0, inB)
    (hvConst (0, inB) (Ctxs w 16))))

/-- The side condition of the external layer with folded constants: `p` fits `2 w` bits
and is at most `2 ^ w`, and the bounds check of `extRcBlk` from `extRcIvs` to
`[0, extOut]`. -/
def RcRed.extOk (w p : ℕ) (R : RcRed) : Bool :=
  decide (p < 2 ^ (2 * w) ∧ p ≤ 2 ^ w) &&
    boundsOk false (extRcIvs w p R.inB) (extRcBlk w p R.extS R.extK R.extM) (0, R.extOut)

/-- The side condition of the internal layer with folded constants: `p` fits `2 w` bits
and is at most `2 ^ w`, and the bounds check of `intRcBlk` from `intRcIvs` to
`[0, intOut]`. -/
def RcRed.intOk (w p : ℕ) (R : RcRed) : Bool :=
  decide (p < 2 ^ (2 * w) ∧ p ≤ 2 ^ w) &&
    boundsOk false (intRcIvs w p R.inB)
      (intRcBlk w p R.mulS R.mulK R.mulM R.intS R.intK R.intM) (0, R.intOut)

/-- **The cross-round bound.** Both layer checks hold, and the bound `B` closes: lanes at
most `B` are admissible inputs (`B ≤ inB`), and both output bounds are at most `B`. -/
def RcRed.Ok (w p B : ℕ) (R : RcRed) : Bool :=
  R.extOk w p && R.intOk w p && decide (B ≤ R.inB ∧ R.extOut ≤ B ∧ R.intOut ≤ B)

/-- On a constant at most `p − 1` and lanes at most `inB`, the output of `extRcBlk` is its
integer semantics and is at most `extOut`. -/
theorem extRcBlk_word {w p : ℕ} (R : RcRed) (h : R.extOk w p = true) (c : BitVec w)
    (hc : c.toNat ≤ p - 1) (g : ℕ → BitVec w) (hg : ∀ j < 20, (g j).toNat ≤ R.inB) :
    ((((extRcBlk w p R.extS R.extK R.extM).denote (.cons c (lanesVal (Rw w) g 20 0))
        : BitVec w).toNat : ℤ)) = extRcZ w p R.extS R.extK R.extM c.toNat
          (fun j => ((g j).toNat : ℤ)) ∧
      ((extRcBlk w p R.extS R.extK R.extM).denote (.cons c (lanesVal (Rw w) g 20 0))
        : BitVec w).toNat ≤ R.extOut := by
  simp only [RcRed.extOk, Bool.and_eq_true] at h
  have hV : ValsIn false (extRcIvs w p R.inB) (.cons c (lanesVal (Rw w) g 20 0)) :=
    ⟨⟨by simp [rd], by simp [rd]; omega⟩, valsIn_lanes g hg⟩
  obtain ⟨h1, -, h3⟩ := denote_eq_denoteZ_of_boundsOk false _ _ _ h.2 _ hV
  rw [extRcBlk_denoteZ] at h1
  simp only [rd, Bool.false_eq_true, ite_false] at h1 h3
  exact ⟨h1, by exact_mod_cast h3⟩

/-- On a constant and a diagonal constant at most `p − 1` and lanes at most `inB`, the
output of `intRcBlk` is its integer semantics and is at most `intOut`. -/
theorem intRcBlk_word {w p : ℕ} (R : RcRed) (h : R.intOk w p = true) (c d x : BitVec w)
    (hc : c.toNat ≤ p - 1) (hd : d.toNat ≤ p - 1) (hx : x.toNat ≤ R.inB) (g : ℕ → BitVec w)
    (hg : ∀ j < 16, (g j).toNat ≤ R.inB) :
    ((((intRcBlk w p R.mulS R.mulK R.mulM R.intS R.intK R.intM).denote
        (.cons c (.cons d (.cons x (lanesVal (Rw w) g 16 0)))) : BitVec w).toNat : ℤ))
        = intRcZ w p R.mulS R.mulK R.mulM R.intS R.intK R.intM c.toNat d.toNat x.toNat
          (fun j => ((g j).toNat : ℤ)) ∧
      ((intRcBlk w p R.mulS R.mulK R.mulM R.intS R.intK R.intM).denote
        (.cons c (.cons d (.cons x (lanesVal (Rw w) g 16 0)))) : BitVec w).toNat
        ≤ R.intOut := by
  simp only [RcRed.intOk, Bool.and_eq_true] at h
  have hV : ValsIn false (intRcIvs w p R.inB)
      (.cons c (.cons d (.cons x (lanesVal (Rw w) g 16 0)))) :=
    ⟨⟨by simp [rd], by simp [rd]; omega⟩, ⟨by simp [rd], by simp [rd]; omega⟩,
      ⟨by simp [rd], by simp [rd]; omega⟩, valsIn_lanes g hg⟩
  obtain ⟨h1, -, h3⟩ := denote_eq_denoteZ_of_boundsOk false _ _ _ h.2 _ hV
  rw [intRcBlk_denoteZ] at h1
  simp only [rd, Bool.false_eq_true, ite_false] at h1 h3
  exact ⟨h1, by exact_mod_cast h3⟩

/-! ## 8. The layers with folded constants on sixteen lanes -/

/-- Lane `i` of a sixteen-lane valuation. -/
abbrev lane {w : ℕ} (W : Valuation (Ctxs w 16)) (i : ℕ) : BitVec w :=
  hvGetG (Rw w) (0 : BitVec w) W i

/-- The sixteen lanes of `W` are at most `B` and represent `u` with factor `κ`: lane `i`
is congruent to `u i · κ` modulo `p`. -/
def Rep16 (p : ℕ) {w : ℕ} (κ : ZMod p) (B : ℕ) (u : Fin 16 → ZMod p)
    (W : Valuation (Ctxs w 16)) : Prop :=
  ∀ i : Fin 16, (lane W i).toNat ≤ B ∧ ((lane W i).toNat : ZMod p) = u i * κ

theorem Rep16.mono {p w : ℕ} {κ : ZMod p} {B B' : ℕ} {u : Fin 16 → ZMod p}
    {W : Valuation (Ctxs w 16)} (h : Rep16 p κ B u W) (hB : B ≤ B') : Rep16 p κ B' u W :=
  fun i => ⟨(h i).1.trans hB, (h i).2⟩

theorem ln_lookup_lane {w : ℕ} (W : Valuation (Ctxs w 16)) {i : ℕ} (hi : i ≤ 15) :
    bv (ln w i) W = lane W i := by
  have e : W = lanesVal (Rw w) (fun j => lane W j) 16 0 :=
    NegacyclicNttTemplate.eq_lanesVal (Rw w) (0 : BitVec w) _ 16 0 W fun j _ => by
      rw [Nat.zero_add]
  conv_lhs => rw [e]
  exact ln_lookup w _ hi

/-- The constants `c i · κ` as canonical residues, `0` past lane 15. -/
def encC {p : ℕ} (κ : ZMod p) (c : Fin 16 → ZMod p) (i : ℕ) : ℕ :=
  if h : i < 16 then (c ⟨i, h⟩ * κ).val else 0

theorem encC_spec {p : ℕ} [NeZero p] (κ : ZMod p) (c : Fin 16 → ZMod p) (i : Fin 16) :
    encC κ c i < p ∧ ((encC κ c i : ℕ) : ZMod p) = c i * κ := by
  simp [encC, ZMod.val_lt]

theorem toNat_ofNat_lt {w n p : ℕ} (hn : n < p) (hp : p ≤ 2 ^ w) :
    (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le hn hp)]

/-- Output lane `i` of the external layer with folded constants `c`: `extRcBlk` on the
constant `c i` and the input lanes `extIdx i`. -/
def extRcLane (w p s k m : ℕ) (c : ℕ → ℕ) (i : ℕ) : Com jasminDialect (Ctxs w 16) (Rw w) :=
  .var (constE w (c i)) ((extRcBlk w p s k m).rename
    (homOf (.cons .here (lanesHV (fun j => .there (ln w (extIdx i j))) 20 0))))

/-- The external layer on sixteen lanes with folded constants `c`. -/
def extRcProg (w p : ℕ) (R : RcRed) (c : ℕ → ℕ) :
    MultiReturnCom jasminDialect (Ctxs w 16) (Ctxs w 16) :=
  laneMapW 16 (extRcLane w p R.extS R.extK R.extM c)

theorem extRcLane_denote (w p s k m : ℕ) (c : ℕ → ℕ) {i : ℕ} (hi : i < 16)
    (g : ℕ → BitVec w) :
    (extRcLane w p s k m c i).denote (lanesVal (Rw w) g 16 0)
      = (extRcBlk w p s k m).denote
          (.cons (BitVec.ofNat w (c i)) (lanesVal (Rw w) (fun j => g (extIdx i j)) 20 0)) := by
  rw [extRcLane, Com.denote, Com.denote_rename, pullV_homOf]
  show (extRcBlk w p s k m).denote (.cons _ (MultiReturnCom.lookupVars _ _)) = _
  rw [lookupVars_lanesHV]
  congr 2
  exact congrArg (fun f => lanesVal (Rw w) f 20 0)
    (funext fun j => ln_lookup w g (extIdx_le i j hi))

/-- Output lane `i` of the internal layer with diagonal constants `dg` and folded
constants `c`: `intRcBlk` on `c i`, `dg i`, lane `i` and the sixteen lanes. -/
def intRcLane (w p s₁ k₁ m₁ s k m : ℕ) (dg c : ℕ → ℕ) (i : ℕ) :
    Com jasminDialect (Ctxs w 16) (Rw w) :=
  .var (constE w (c i)) <| .var (constE w (dg i)) <|
  (intRcBlk w p s₁ k₁ m₁ s k m).rename (homOf (.cons (.there .here) (.cons .here
    (.cons (.there (.there (ln w i))) (lanesHV (fun j => .there (.there (ln w j))) 16 0)))))

/-- The internal layer on sixteen lanes with diagonal constants `dg` and folded
constants `c`. -/
def intRcProg (w p : ℕ) (R : RcRed) (dg c : ℕ → ℕ) :
    MultiReturnCom jasminDialect (Ctxs w 16) (Ctxs w 16) :=
  laneMapW 16 (intRcLane w p R.mulS R.mulK R.mulM R.intS R.intK R.intM dg c)

theorem intRcLane_denote (w p s₁ k₁ m₁ s k m : ℕ) (dg c : ℕ → ℕ) {i : ℕ} (hi : i ≤ 15)
    (g : ℕ → BitVec w) :
    (intRcLane w p s₁ k₁ m₁ s k m dg c i).denote (lanesVal (Rw w) g 16 0)
      = (intRcBlk w p s₁ k₁ m₁ s k m).denote (.cons (BitVec.ofNat w (c i))
          (.cons (BitVec.ofNat w (dg i)) (.cons (g i) (lanesVal (Rw w) g 16 0)))) := by
  rw [intRcLane, Com.denote, Com.denote, Com.denote_rename, pullV_homOf]
  show (intRcBlk w p s₁ k₁ m₁ s k m).denote
    (.cons _ (.cons _ (.cons _ (MultiReturnCom.lookupVars _ _)))) = _
  rw [lookupVars_lanesHV]
  congr 3
  exact congrArg₂ HVector.cons (ln_lookup w g hi)
    (lanesVal_congr 16 0 fun j _ hj => ln_lookup w g (by omega))

/-- On input lanes at most `inB` and constants below `p`, every output lane of `extRcProg`
is at most `extOut` and is the lane of `externalMDS` plus the constant modulo `p`. -/
theorem extRcProg_lane {w : ℕ} (P : Params) (R : RcRed) (h : R.extOk w P.p = true)
    (c : ℕ → ℕ) (hc : ∀ i < 16, c i < P.p) (g : ℕ → BitVec w)
    (hg : ∀ j < 16, (g j).toNat ≤ R.inB) (i : Fin 16) :
    (lane ((extRcProg w P.p R c).denote (lanesVal (Rw w) g 16 0)) i).toNat ≤ R.extOut ∧
      ((lane ((extRcProg w P.p R c).denote (lanesVal (Rw w) g 16 0)) i).toNat : ZMod P.p)
        = externalMDS (P := P) (fun j => ((g j).toNat : ZMod P.p)) i + (c i : ZMod P.p) := by
  have hpw : P.p < 2 ^ (2 * w) ∧ P.p ≤ 2 ^ w := by
    simp only [RcRed.extOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have hc' := toNat_ofNat_lt (w := w) (hc i i.isLt) hpw.2
  simp only [lane]
  rw [extRcProg, laneMapW_denote, hvGetG_denoteN (Rw w) (0 : BitVec w) 16 _ _ i i.isLt,
    extRcLane_denote _ _ _ _ _ _ i.isLt]
  obtain ⟨e, hb⟩ := extRcBlk_word R h (BitVec.ofNat w (c i))
    (by rw [hc']; have := hc i i.isLt; omega) (fun j => g (extIdx i j))
    (fun j _ => hg _ (Nat.lt_succ_of_le (extIdx_le i j i.isLt)))
  refine ⟨hb, ?_⟩
  rw [← Int.cast_natCast, e, extRcZ, redZ_cast w P.p _ _ _ hpw.1, hc',
    externalMDS_eq (fun j => ((g j).toNat : ZMod P.p))]
  push_cast [rowZ, rowF]
  rfl

/-- On input lanes at most `inB`, diagonal constants `dg` that are residues of the diagonal
of `P` and constants below `p`, every output lane of `intRcProg` is at most `intOut` and is
the lane of `internalMDS P` plus the constant modulo `p`. -/
theorem intRcProg_lane {w : ℕ} (P : Params) (R : RcRed) (h : R.intOk w P.p = true)
    (dg c : ℕ → ℕ) (hdg : ∀ i : Fin 16, dg i < P.p ∧ ((dg i : ℕ) : ZMod P.p) = P.diag i)
    (hc : ∀ i < 16, c i < P.p) (g : ℕ → BitVec w) (hg : ∀ j < 16, (g j).toNat ≤ R.inB)
    (i : Fin 16) :
    (lane ((intRcProg w P.p R dg c).denote (lanesVal (Rw w) g 16 0)) i).toNat ≤ R.intOut ∧
      ((lane ((intRcProg w P.p R dg c).denote (lanesVal (Rw w) g 16 0)) i).toNat : ZMod P.p)
        = internalMDS P (fun j => ((g j).toNat : ZMod P.p)) i + (c i : ZMod P.p) := by
  have hi : i.val ≤ 15 := Nat.le_of_lt_succ i.isLt
  have hpw : P.p < 2 ^ (2 * w) ∧ P.p ≤ 2 ^ w := by
    simp only [RcRed.intOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have hc' := toNat_ofNat_lt (w := w) (hc i i.isLt) hpw.2
  have hd' := toNat_ofNat_lt (w := w) (hdg i).1 hpw.2
  simp only [lane]
  rw [intRcProg, laneMapW_denote, hvGetG_denoteN (Rw w) (0 : BitVec w) 16 _ _ i i.isLt,
    intRcLane_denote _ _ _ _ _ _ _ _ dg c hi]
  obtain ⟨e, hb⟩ := intRcBlk_word R h (BitVec.ofNat w (c i)) (BitVec.ofNat w (dg i)) (g i)
    (by rw [hc']; have := hc i i.isLt; omega) (by rw [hd']; have := (hdg i).1; omega)
    (hg i i.isLt) g hg
  refine ⟨hb, ?_⟩
  rw [← Int.cast_natCast, e, intRcZ, redZ_cast w P.p _ _ _ hpw.1, hc', hd']
  push_cast [sum16Z]
  rw [redZ_cast w P.p _ _ _ hpw.1]
  push_cast
  rw [(hdg i).2, ← add_assoc]
  congr 1

/-! ## 9. Linearity of the layers in the factor -/

theorem mat4_mul {P : Params} (a b c d κ : ZMod P.p) (j : Fin 4) :
    mat4 (P := P) (a * κ) (b * κ) (c * κ) (d * κ) j = mat4 (P := P) a b c d j * κ := by
  fin_cases j <;> simp [mat4] <;> ring

theorem externalMDS_mul {P : Params} (u : Fin 16 → ZMod P.p) (κ : ZMod P.p) (i : Fin 16) :
    externalMDS (P := P) (fun j => u j * κ) i = externalMDS (P := P) u i * κ := by
  simp only [externalMDS, colSumMap, mdsPre, mat4_mul]
  ring

theorem internalMDS_mul (P : Params) (u : Fin 16 → ZMod P.p) (κ : ZMod P.p) (i : Fin 16) :
    internalMDS P (fun j => u j * κ) i = internalMDS P u i * κ := by
  simp only [internalMDS, sumAll]
  ring

/-- **The external layer with folded constants.** On lanes at most `B ≤ inB` representing
`u` with factor `κ`, the output lanes of `extRcProg` with the constants `c · κ` are at most
`extOut` and represent `externalMDS u + c` with factor `κ`. -/
theorem extRcProg_rep {w : ℕ} (P : Params) [NeZero P.p] (R : RcRed)
    (h : R.extOk w P.p = true) {κ : ZMod P.p} {B : ℕ} (hB : B ≤ R.inB)
    (c : Fin 16 → ZMod P.p) {u : Fin 16 → ZMod P.p} {W : Valuation (Ctxs w 16)}
    (hW : Rep16 P.p κ B u W) :
    Rep16 P.p κ R.extOut (fun i => externalMDS u i + c i)
      ((extRcProg w P.p R (encC κ c)).denote W) := by
  intro i
  have e : W = lanesVal (Rw w) (fun j => lane W j) 16 0 :=
    NegacyclicNttTemplate.eq_lanesVal (Rw w) (0 : BitVec w) _ 16 0 W fun j _ => by
      rw [Nat.zero_add]
  have hrep : (fun j : Fin 16 => ((lane W j).toNat : ZMod P.p)) = fun j => u j * κ :=
    funext fun j => (hW j).2
  obtain ⟨hb, hv⟩ := extRcProg_lane P R h (encC κ c) (fun i hi => (encC_spec κ c ⟨i, hi⟩).1)
    (fun j => lane W j) (fun j hj => ((hW ⟨j, hj⟩).1).trans hB) i
  rw [← e] at hb hv
  refine ⟨hb, ?_⟩
  rw [hv, (encC_spec κ c i).2, hrep, externalMDS_mul]
  ring

/-- **The internal layer with folded constants.** On lanes at most `B ≤ inB` representing
`u` with factor `κ`, the output lanes of `intRcProg` with the diagonal of `P` and the
constants `c · κ` are at most `intOut` and represent `internalMDS P u + c` with
factor `κ`. -/
theorem intRcProg_rep {w : ℕ} (P : Params) [NeZero P.p] (R : RcRed)
    (h : R.intOk w P.p = true) {κ : ZMod P.p} {B : ℕ} (hB : B ≤ R.inB)
    (c : Fin 16 → ZMod P.p) {u : Fin 16 → ZMod P.p} {W : Valuation (Ctxs w 16)}
    (hW : Rep16 P.p κ B u W) :
    Rep16 P.p κ R.intOut (fun i => internalMDS P u i + c i)
      ((intRcProg w P.p R (diagNat P) (encC κ c)).denote W) := by
  intro i
  have e : W = lanesVal (Rw w) (fun j => lane W j) 16 0 :=
    NegacyclicNttTemplate.eq_lanesVal (Rw w) (0 : BitVec w) _ 16 0 W fun j _ => by
      rw [Nat.zero_add]
  have hrep : (fun j : Fin 16 => ((lane W j).toNat : ZMod P.p)) = fun j => u j * κ :=
    funext fun j => (hW j).2
  obtain ⟨hb, hv⟩ := intRcProg_lane P R h (diagNat P) (encC κ c) (diagNat_spec P)
    (fun i hi => (encC_spec κ c ⟨i, hi⟩).1) (fun j => lane W j)
    (fun j hj => ((hW ⟨j, hj⟩).1).trans hB) i
  rw [← e] at hb hv
  refine ⟨hb, ?_⟩
  rw [hv, (encC_spec κ c i).2, hrep, internalMDS_mul]
  ring

/-! ## 10. The S-box layer and the rounds -/

/-- Lane `i` of the S-box layer: the S-box program on lane `i` when the layer is full or
`i = 0`, else lane `i`. -/
def sboxLane {w p : ℕ} (M : ChainMul w p) (bits : List Bool) (full : Bool) (i : ℕ) :
    Com jasminDialect (Ctxs w 16) (Rw w) :=
  if full = true ∨ i = 0 then (sboxProg M bits).rename (homOf (.cons (ln w i) .nil))
  else .ret (ln w i)

/-- The S-box layer on sixteen lanes, on every lane (`full`) or on lane 0. -/
def sboxLayerProg {w p : ℕ} (M : ChainMul w p) (bits : List Bool) (full : Bool) :
    MultiReturnCom jasminDialect (Ctxs w 16) (Ctxs w 16) :=
  laneMapW 16 (sboxLane M bits full)

/-- **The S-box layer.** On lanes at most the chain bound representing `u` with factor
`κ`, the output lanes are at most the chain bound and represent `u` with the S-box applied
on every lane (`full`) or on lane 0. -/
theorem sboxLayerProg_rep {w : ℕ} (P : Params) (M : ChainMul w P.p) (bits : List Bool)
    (hd : nexp bits 0 + 1 = P.sboxDeg) {κ' : ZMod P.p} (hκ : M.κ * κ' = 1) (full : Bool)
    {u : Fin 16 → ZMod P.p} {W : Valuation (Ctxs w 16)} (hW : Rep16 P.p M.κ M.bound u W) :
    Rep16 P.p M.κ M.bound (fun i => if full = true ∨ i.val = 0 then sbox P (u i) else u i)
      ((sboxLayerProg M bits full).denote W) := by
  intro i
  have hl := ln_lookup_lane W (Nat.le_of_lt_succ i.isLt)
  simp only [lane]
  rw [sboxLayerProg, laneMapW_denote, hvGetG_denoteN (Rw w) (0 : BitVec w) 16 _ _ i i.isLt,
    sboxLane]
  by_cases hc : full = true ∨ i.val = 0
  · rw [ite_eq_left hc, ite_eq_left hc, Com.denote_rename, pullV_homOf]
    have hx : (MultiReturnCom.lookupVars (.cons (ln w i) .nil) W : Valuation (C1 w))
        = .cons (lane W i) .nil := by
      rw [← hl]
      rfl
    rw [hx]
    exact sboxProg_sbox P M bits hd hκ _ (hW i).1 (hW i).2
  · rw [ite_eq_right hc, ite_eq_right hc]
    show (bv (ln w i) W).toNat ≤ M.bound ∧ ((bv (ln w i) W).toNat : ZMod P.p) = u i * M.κ
    rw [hl]
    exact hW i

/-- A round of the permutation: full (S-box on every lane, external layer) or partial
(S-box on lane 0, internal layer), with the constant vector `c` added before the S-box. -/
structure Step (P : Params) where
  /-- Whether the round is full. -/
  full : Bool
  /-- The constant vector. -/
  c : Fin 16 → ZMod P.p

/-- The state after the constants and the S-box layer of `st`. -/
def Step.pre {P : Params} (st : Step P) (s : Fin 16 → ZMod P.p) : Fin 16 → ZMod P.p :=
  fun i => if st.full = true ∨ i.val = 0 then sbox P (s i + st.c i) else s i + st.c i

/-- The round `st` on the state `s`. -/
def Step.apply {P : Params} (st : Step P) (s : Fin 16 → ZMod P.p) : Fin 16 → ZMod P.p :=
  if st.full then externalMDS (st.pre s) else internalMDS P (st.pre s)

theorem Step.apply_full {P : Params} (c s : Fin 16 → ZMod P.p) :
    (⟨true, c⟩ : Step P).apply s = externalRound P s c := by
  simp only [Step.apply, externalRound, ↓reduceIte]
  congr 1

theorem Step.apply_partial {P : Params} (c : ZMod P.p) (s : Fin 16 → ZMod P.p) :
    (⟨false, fun i => if i.val = 0 then c else 0⟩ : Step P).apply s = internalRound P s c := by
  simp only [Step.apply, internalRound, Bool.false_eq_true, ↓reduceIte]
  congr 1
  funext i
  by_cases h : i.val = 0 <;> simp [Step.pre, h]

/-- The rounds of `permute P` after the initial external layer: the first half of the
full rounds, the partial rounds, the second half of the full rounds. -/
def steps (P : Params) : List (Step P) :=
  (List.finRange P.halfFullRounds).map (fun r => ⟨true, rcInitial P r⟩) ++
    (List.finRange P.partialRounds).map
      (fun r => ⟨false, fun i => if i.val = 0 then P.rcInternal r else 0⟩) ++
    (List.finRange P.halfFullRounds).map (fun r => ⟨true, rcFinal P r⟩)

/-- `permute P` is the fold of the rounds `steps P` from the initial external layer. -/
theorem permute_eq_steps (P : Params) (x : Fin 16 → ZMod P.p) :
    permute P x = (steps P).foldl (fun s st => st.apply s) (externalMDS x) := by
  simp only [permute, steps, List.foldl_append, List.foldl_map, Step.apply_full,
    Step.apply_partial]

/-- The program of one round: the S-box layer, then the linear layer of the round with the
next constant vector `c` folded in. -/
def roundProg {w : ℕ} (P : Params) (M : ChainMul w P.p) (bits : List Bool) (R : RcRed)
    (full : Bool) (c : Fin 16 → ZMod P.p) :
    MultiReturnCom jasminDialect (Ctxs w 16) (Ctxs w 16) :=
  mrSeq (sboxLayerProg M bits full)
    (if full then extRcProg w P.p R (encC M.κ c)
      else intRcProg w P.p R (diagNat P) (encC M.κ c))

/-- **One round.** Under `R.Ok` at the chain bound, lanes at most the bound representing
`s + st.c` give lanes at most the bound representing `st.apply s + c`. -/
theorem roundProg_rep {w : ℕ} (P : Params) [NeZero P.p] (M : ChainMul w P.p)
    (bits : List Bool) (hd : nexp bits 0 + 1 = P.sboxDeg) {κ' : ZMod P.p}
    (hκ : M.κ * κ' = 1) (R : RcRed) (hR : R.Ok w P.p M.bound = true) (st : Step P)
    (c : Fin 16 → ZMod P.p) {s : Fin 16 → ZMod P.p} {W : Valuation (Ctxs w 16)}
    (hW : Rep16 P.p M.κ M.bound (fun i => s i + st.c i) W) :
    Rep16 P.p M.κ M.bound (fun i => st.apply s i + c i)
      ((roundProg P M bits R st.full c).denote W) := by
  simp only [RcRed.Ok, Bool.and_eq_true, decide_eq_true_eq] at hR
  obtain ⟨⟨hE, hI⟩, hB, hEo, hIo⟩ := hR
  have h1 := sboxLayerProg_rep P M bits hd hκ st.full hW
  change Rep16 P.p M.κ M.bound (st.pre s) _ at h1
  obtain ⟨full, c0⟩ := st
  cases full
  · rw [roundProg, mrSeq_denote]
    exact (intRcProg_rep P R hI hB c h1).mono hIo
  · rw [roundProg, mrSeq_denote]
    exact (extRcProg_rep P R hE hB c h1).mono hEo

/-- The rounds `st :: rest`, each with the constant vector of the next round folded into
its linear layer, and `cf` folded into the last. -/
def roundsProg {w : ℕ} (P : Params) (M : ChainMul w P.p) (bits : List Bool) (R : RcRed) :
    Step P → List (Step P) → (Fin 16 → ZMod P.p) →
      MultiReturnCom jasminDialect (Ctxs w 16) (Ctxs w 16)
  | st, [], cf => roundProg P M bits R st.full cf
  | st, st' :: rest, cf =>
    mrSeq (roundProg P M bits R st.full st'.c) (roundsProg P M bits R st' rest cf)

/-- **The rounds.** Lanes at most the bound representing `s + st.c` give lanes at most the
bound representing the fold of `st :: rest` from `s`, plus `cf`. -/
theorem roundsProg_rep {w : ℕ} (P : Params) [NeZero P.p] (M : ChainMul w P.p)
    (bits : List Bool) (hd : nexp bits 0 + 1 = P.sboxDeg) {κ' : ZMod P.p}
    (hκ : M.κ * κ' = 1) (R : RcRed) (hR : R.Ok w P.p M.bound = true)
    (cf : Fin 16 → ZMod P.p) :
    ∀ (rest : List (Step P)) (st : Step P) (s : Fin 16 → ZMod P.p)
      (W : Valuation (Ctxs w 16)), Rep16 P.p M.κ M.bound (fun i => s i + st.c i) W →
      Rep16 P.p M.κ M.bound
        (fun i => (st :: rest).foldl (fun s st => st.apply s) s i + cf i)
        ((roundsProg P M bits R st rest cf).denote W)
  | [], st, _, _, hW => roundProg_rep P M bits hd hκ R hR st cf hW
  | st' :: rest, st, s, _, hW => by
    rw [roundsProg, mrSeq_denote]
    exact roundsProg_rep P M bits hd hκ R hR cf rest st' (st.apply s) _
      (roundProg_rep P M bits hd hκ R hR st st'.c hW)

/-- The permutation program on the round list `l`: the initial external layer with the
constants of the first round folded in, then the rounds. -/
def permProgOf {w : ℕ} (P : Params) (M : ChainMul w P.p) (bits : List Bool) (R : RcRed) :
    List (Step P) → MultiReturnCom jasminDialect (Ctxs w 16) (Ctxs w 16)
  | [] => extRcProg w P.p R (encC M.κ 0)
  | st :: rest => mrSeq (extRcProg w P.p R (encC M.κ st.c)) (roundsProg P M bits R st rest 0)

/-- **The Poseidon2 permutation at width 16** as a word program: `permProgOf` on the rounds
of `P`. -/
def permProg {w : ℕ} (P : Params) (M : ChainMul w P.p) (bits : List Bool) (R : RcRed) :
    MultiReturnCom jasminDialect (Ctxs w 16) (Ctxs w 16) :=
  permProgOf P M bits R (steps P)

theorem permProgOf_rep {w : ℕ} (P : Params) [NeZero P.p] (M : ChainMul w P.p)
    (bits : List Bool) (hd : nexp bits 0 + 1 = P.sboxDeg) {κ' : ZMod P.p}
    (hκ : M.κ * κ' = 1) (R : RcRed) (hR : R.Ok w P.p M.bound = true)
    (x : Fin 16 → ZMod P.p) (W : Valuation (Ctxs w 16)) (hW : Rep16 P.p M.κ M.bound x W) :
    ∀ l : List (Step P), Rep16 P.p M.κ M.bound
      (l.foldl (fun s st => st.apply s) (externalMDS x)) ((permProgOf P M bits R l).denote W)
  | [] => by
    have hR' := hR
    simp only [RcRed.Ok, Bool.and_eq_true, decide_eq_true_eq] at hR'
    have := (extRcProg_rep P R hR'.1.1 hR'.2.1 0 hW).mono hR'.2.2.1
    simp only [Pi.zero_apply, add_zero] at this
    exact this
  | st :: rest => by
    have hR' := hR
    simp only [RcRed.Ok, Bool.and_eq_true, decide_eq_true_eq] at hR'
    rw [permProgOf, mrSeq_denote]
    have := roundsProg_rep P M bits hd hκ R hR 0 rest st (externalMDS x) _
      ((extRcProg_rep P R hR'.1.1 hR'.2.1 st.c hW).mono hR'.2.2.1)
    simpa using this

/-- **The permutation.** Under `R.Ok` at the chain bound `B` of `M`, input lanes at most
`B` representing `x` with factor `κ` give output lanes at most `B` representing
`permute P x` with factor `κ`. -/
theorem permProg_spec {w : ℕ} (P : Params) [NeZero P.p] (M : ChainMul w P.p)
    (bits : List Bool) (hd : nexp bits 0 + 1 = P.sboxDeg) {κ' : ZMod P.p}
    (hκ : M.κ * κ' = 1) (R : RcRed) (hR : R.Ok w P.p M.bound = true)
    (x : Fin 16 → ZMod P.p) (W : Valuation (Ctxs w 16)) (hW : Rep16 P.p M.κ M.bound x W) :
    Rep16 P.p M.κ M.bound (permute P x) ((permProg P M bits R).denote W) := by
  rw [permute_eq_steps]
  exact permProgOf_rep P M bits hd hκ R hR x W hW (steps P)

/-! ## 11. Instances -/

/-- The BabyBear width-16 parameters of `Width16`, from the constants of
`Hash.Poseidon2.BabyBear`. -/
def bbParams : Params where
  p := CatCrypt.Crypto.Hash.Poseidon2.BabyBear.babyBearPrime
  sboxDeg := 7
  halfFullRounds := 4
  partialRounds := 13
  rcExternal r := CatCrypt.Crypto.Hash.Poseidon2.BabyBear.fullRoundConstants ⟨r.val, by
    have := r.isLt; unfold CatCrypt.Crypto.Hash.Poseidon2.BabyBear.fullRounds; omega⟩
  rcInternal r := CatCrypt.Crypto.Hash.Poseidon2.BabyBear.partialRoundConstants ⟨r.val, by
    have := r.isLt; unfold CatCrypt.Crypto.Hash.Poseidon2.BabyBear.partialRounds; omega⟩
  diag := CatCrypt.Crypto.Hash.Poseidon2.BabyBear.diagV

instance bbParams_neZero : NeZero bbParams.p := ⟨by decide⟩

instance kbParams_neZero : NeZero CatCrypt.Crypto.Hash.Poseidon2.KoalaBear.params.p :=
  ⟨by decide⟩

/-- BabyBear with input bound `p + 64`. -/
def bbFieldB : WordField 32 2013265921 := { babyBearField with inMax := 2013265985 }

/-- KoalaBear with input bound `p + 64`. -/
def kbFieldB : WordField 32 2130706433 := { koalaBearField with inMax := 2130706497 }

/-- The linear layers at BabyBear with folded constants, lanes at most `p + 64`. -/
def bbRc : RcRed :=
  ⟨2013265985, 4, 58, 2290649223, 2013265949, 29, 33, 2290649223, 3, 59, 2290649223,
    2013265935⟩

/-- The linear layers at KoalaBear with folded constants, lanes at most `p + 64`. -/
def kbRc : RcRed :=
  ⟨2130706497, 4, 58, 2164392967, 2130706450, 29, 33, 2164392967, 3, 59, 2164392967,
    2130706441⟩

theorem bbFieldB_plantOk : bbFieldB.plantOk = true := by decide +kernel
theorem kbFieldB_plantOk : kbFieldB.plantOk = true := by decide +kernel
theorem bbRc_ok : bbRc.Ok 32 2013265921 2013265985 = true := by decide +kernel
theorem kbRc_ok : kbRc.Ok 32 2130706433 2130706497 = true := by decide +kernel

/-- The S-box chain of the BabyBear permutation: Plantard multiplies on inputs at most
`p + 64`. -/
def bbPermChain : ChainMul 32 2013265921 := plantChain bbFieldB bbFieldB_plantOk (by decide)

/-- The S-box chain of the KoalaBear permutation: Plantard multiplies on inputs at most
`p + 64`. -/
def kbPermChain : ChainMul 32 2130706433 := plantChain kbFieldB kbFieldB_plantOk (by decide)

/-- **The BabyBear permutation.** Input lanes at most `p + 64` representing `x` with factor
`−2 ^ 64` give output lanes at most `p + 64` representing `permute bbParams x`. -/
theorem bbPermProg_spec (x : Fin 16 → ZMod bbParams.p) (W : Valuation (Ctxs 32 16))
    (hW : Rep16 bbParams.p (-2 ^ 64) 2013265985 x W) :
    Rep16 bbParams.p (-2 ^ 64) 2013265985 (permute bbParams x)
      ((permProg bbParams bbPermChain [true, true] bbRc).denote W) :=
  permProg_spec bbParams bbPermChain [true, true] rfl (κ' := 442368000) (by decide +kernel)
    bbRc bbRc_ok x W hW

/-- **The KoalaBear permutation.** Input lanes at most `p + 64` representing `x` with factor
`−2 ^ 64` give output lanes at most `p + 64` representing `KoalaBear.permute x`. -/
theorem kbPermProg_spec (x : Fin 16 → ZMod CatCrypt.Crypto.Hash.Poseidon2.KoalaBear.P)
    (W : Valuation (Ctxs 32 16))
    (hW : Rep16 CatCrypt.Crypto.Hash.Poseidon2.KoalaBear.P (-2 ^ 64) 2130706497 x W) :
    Rep16 CatCrypt.Crypto.Hash.Poseidon2.KoalaBear.P (-2 ^ 64) 2130706497
      (CatCrypt.Crypto.Hash.Poseidon2.KoalaBear.permute x)
      ((permProg CatCrypt.Crypto.Hash.Poseidon2.KoalaBear.params kbPermChain [true]
        kbRc).denote W) :=
  permProg_spec CatCrypt.Crypto.Hash.Poseidon2.KoalaBear.params kbPermChain [true] rfl
    (κ' := 524386048) (by decide +kernel) kbRc kbRc_ok x W hW

end CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Word
