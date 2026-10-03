/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NarrowFieldZk
public import CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord
public import CatCrypt.Crypto.Hash.Poseidon2.Width16

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
  colSumMap mat4 sumAll)

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
  simp only [rdT, rd, Bool.false_eq_true, if_false]
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
  simp only [rd, Bool.false_eq_true, if_false]
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
  simp only [rd, Bool.false_eq_true, if_false] at h1 h3
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
  simp only [rd, Bool.false_eq_true, if_false] at h1 h3
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

end CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Word
