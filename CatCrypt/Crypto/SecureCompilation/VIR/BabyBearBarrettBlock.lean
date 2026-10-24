/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RangeDomain
public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2WholePermCom

/-!
# Barrett reduction block for the BabyBear field multiply

`bbBarrett` reduces a product `x < p²` of two reduced BabyBear words modulo
`p = 2013265921 = 15·2²⁷ + 1` by one Barrett quotient estimate and one conditional
subtract:

* `h = x >>> 30` (below `2³²`),
* `q = (h · μ) >>> 32` with `μ = ⌊2⁶² / p⌋ = 2290649223` (below `2³²`),
* `r = x − q · p`, which lies in `[0, 2p)`,
* `bbCsub r`.

Both multiplications take operands below `2³²` (`bbBarrett_mulHi_operands_lt`,
`bbBarrett_mulQ_operands_lt`), so each is the low half of a 32 × 32 → 64 product.

`emitReduceBarrett` and `emitMulBarrett` are the builder blocks in the
continuation-passing `BState` style of `Poseidon2WholePermCom`, using the scratch
slots `sc0`, `sc1` (and `sc2` inside `emitCsub`). `emitMulBarrett_denote_ret`
states that the block computes `bbMul` on reduced inputs.

## Main results

* `barrett_quot_bounds`: `q · p ≤ x < q · p + 2p` for `x < p²`, an instance of the
  two-shift Barrett bound `RangeDomain.barrett_nat`.
* `bbBarrett_toNat`: `(bbBarrett x).toNat = x.toNat % p` for `x.toNat < p²`.
* `bbBarrett_mul_eq_bbMul`: `bbBarrett (a * b) = bbMul a b` on reduced words.
* `emitReduceBarrett_denote_ret`, `emitMulBarrett_denote_ret`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.BabyBearBarrettBlock

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit (bbP bbCsub bbMul r64)
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2BbMulFieldExact
  (bbP_toNat bbCsub_toNat_of_lt_2p bbMul_toNat mul_toNat_of_lt_p)
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2WholePermCom
  (BState Cont emitBin emitConst emitCsub emitCsub_denote_ret slotVal slotVal_step
   emitBin_denote emitConst_denote here_lookup there_lookup headVar sc0 sc1 sc2 cP)
open CatCrypt.Crypto.SecureCompilation.RangeDomain (barrett_nat barrettBound)

/-! ## 1. The Barrett quotient on natural numbers -/

/-- The Barrett constant `μ = ⌊2⁶² / p⌋` for the BabyBear prime. -/
def bbMuNat : Nat := 2290649223

theorem bbMuNat_eq : bbMuNat = 2 ^ 62 / 2013265921 := by
  unfold bbMuNat; norm_num

/-- The Barrett quotient estimate `⌊⌊x / 2³⁰⌋ · μ / 2³²⌋`. -/
def barrettQuot (x : Nat) : Nat := x / 2 ^ 30 * bbMuNat / 2 ^ 32

/-- **Barrett quotient bounds.** For `x < p²` the estimate `q` satisfies
    `q · p ≤ x < q · p + 2p`, so `x − q · p` lies in `[0, 2p)`. The instance of
    `RangeDomain.barrett_nat` at `s = 30`, `t = 32`, `X = p² − 1`, whose remainder
    bound lies below `2p`. -/
theorem barrett_quot_bounds (x : Nat) (hx : x < 2013265921 * 2013265921) :
    barrettQuot x * 2013265921 ≤ x ∧ x < barrettQuot x * 2013265921 + 2 * 2013265921 := by
  obtain ⟨h1, h2⟩ := barrett_nat x (2013265921 * 2013265921 - 1) 30 32 bbMuNat 2013265921
    (by omega) (by norm_num [bbMuNat])
  have hb : barrettBound (2013265921 * 2013265921 - 1) 30 32 bbMuNat 2013265921
      < 2 * 2013265921 := by norm_num [barrettBound, bbMuNat]
  unfold barrettQuot
  omega

theorem barrettQuot_lt (x : Nat) (hx : x < 2013265921 * 2013265921) :
    barrettQuot x < 2013265921 := by
  have := (barrett_quot_bounds x hx).1
  omega

/-! ## 2. The word function -/

/-- The Barrett constant `μ` as a 64-bit word. -/
def bbMu : BitVec 64 := 2290649223

/-- The high part `x >>> 30`, the first multiplication's variable operand. -/
def bbBarrettHi (x : BitVec 64) : BitVec 64 := x >>> (30 : Nat)

/-- The quotient estimate `((x >>> 30) · μ) >>> 32`, the second multiplication's
    variable operand. -/
def bbBarrettQ (x : BitVec 64) : BitVec 64 := (bbBarrettHi x * bbMu) >>> (32 : Nat)

/-- BabyBear Barrett reduction `bbCsub (x − q · p)` with `q = bbBarrettQ x`. -/
def bbBarrett (x : BitVec 64) : BitVec 64 := bbCsub (x - bbBarrettQ x * bbP)

theorem bbMu_toNat : bbMu.toNat = 2290649223 := by decide

theorem bbBarrettHi_toNat (x : BitVec 64) : (bbBarrettHi x).toNat = x.toNat / 2 ^ 30 := by
  simp [bbBarrettHi, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bbBarrettQ_toNat (x : BitVec 64) (hx : x.toNat < 2013265921 * 2013265921) :
    (bbBarrettQ x).toNat = barrettQuot x.toNat := by
  unfold bbBarrettQ barrettQuot bbMuNat
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul,
    bbBarrettHi_toNat, bbMu_toNat, Nat.mod_eq_of_lt (by omega)]

/-- The first multiplication `(x >>> 30) · μ` has both operands below `2³²`. -/
theorem bbBarrett_mulHi_operands_lt (x : BitVec 64)
    (hx : x.toNat < 2013265921 * 2013265921) :
    (bbBarrettHi x).toNat < 2 ^ 32 ∧ bbMu.toNat < 2 ^ 32 := by
  rw [bbBarrettHi_toNat, bbMu_toNat]
  omega

/-- The second multiplication `q · p` has both operands below `2³²`. -/
theorem bbBarrett_mulQ_operands_lt (x : BitVec 64)
    (hx : x.toNat < 2013265921 * 2013265921) :
    (bbBarrettQ x).toNat < 2 ^ 32 ∧ bbP.toNat < 2 ^ 32 := by
  rw [bbBarrettQ_toNat x hx, bbP_toNat]
  have := barrettQuot_lt x.toNat hx
  omega

/-- The remainder `x − q · p` before the conditional subtract, as a natural number. -/
theorem bbBarrett_rem_toNat (x : BitVec 64) (hx : x.toNat < 2013265921 * 2013265921) :
    (x - bbBarrettQ x * bbP).toNat = x.toNat - barrettQuot x.toNat * 2013265921 := by
  have hb := barrett_quot_bounds x.toNat hx
  have hqp : (bbBarrettQ x * bbP).toNat = barrettQuot x.toNat * 2013265921 := by
    rw [BitVec.toNat_mul, bbBarrettQ_toNat x hx, bbP_toNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hqp]; exact hb.1), hqp]

/-- **Barrett reduction is reduction modulo `p`** below `p²`. -/
theorem bbBarrett_toNat (x : BitVec 64) (hx : x.toNat < 2013265921 * 2013265921) :
    (bbBarrett x).toNat = x.toNat % 2013265921 := by
  have hb := barrett_quot_bounds x.toNat hx
  unfold bbBarrett
  rw [bbCsub_toNat_of_lt_2p _ (by rw [bbBarrett_rem_toNat x hx]; omega),
    bbBarrett_rem_toNat x hx]
  omega

/-- **Barrett reduction of a product of reduced words is `bbMul`.** -/
theorem bbBarrett_mul_eq_bbMul (a b : BitVec 64) (ha : a.toNat < 2013265921)
    (hb : b.toNat < 2013265921) : bbBarrett (a * b) = bbMul a b := by
  apply BitVec.eq_of_toNat_eq
  have hab : (a * b).toNat = a.toNat * b.toNat := mul_toNat_of_lt_p a b ha hb
  rw [bbMul_toNat a b ha hb, bbBarrett_toNat _ (by rw [hab]; exact Nat.mul_lt_mul'' ha hb),
    hab]

/-! ## 3. The builder blocks -/

/-- The Barrett reduction block writing `bbBarrett src` to `dst`:

* `sc0 = 30`, `sc1 = src >>> sc0`;
* `sc0 = μ`, `sc1 = sc1 * sc0`;
* `sc0 = 32`, `sc1 = sc1 >>> sc0`;
* `sc0 = P`, `sc1 = sc1 * sc0`;
* `dst = src - sc1`, then `emitCsub dst dst`. -/
def emitReduceBarrett {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst src : Fin 25) (k : Cont t) : Com jasminDialect Γ t :=
  emitConst st sc0 30 fun s1 =>
  emitBin s1 .shr sc1 src sc0 fun s2 =>
  emitConst s2 sc0 bbMuNat fun s3 =>
  emitBin s3 .mul sc1 sc1 sc0 fun s4 =>
  emitConst s4 sc0 32 fun s5 =>
  emitBin s5 .shr sc1 sc1 sc0 fun s6 =>
  emitConst s6 sc0 cP fun s7 =>
  emitBin s7 .mul sc1 sc1 sc0 fun s8 =>
  emitBin s8 .sub dst src sc1 fun s9 =>
  emitCsub s9 dst dst k

/-- The BabyBear multiply block: `dst = a * b`, then `emitReduceBarrett dst dst`. -/
def emitMulBarrett {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (dst a b : Fin 25) (k : Cont t) : Com jasminDialect Γ t :=
  emitBin st .mul dst a b fun s1 =>
  emitReduceBarrett s1 dst dst k

/-- **`emitReduceBarrett` computes `bbBarrett` at `dst`** (read by a `ret dst`
    continuation), when `dst` is distinct from `sc0`, `sc1`, `sc2` and `src` from
    `sc0`, `sc1`. -/
theorem emitReduceBarrett_denote_ret {Γ : Ctxt jasminDialect}
    (st : BState Γ) (V : Ctxt.Valuation Γ) (dst src : Fin 25)
    (hd0 : dst ≠ sc0) (hd1 : dst ≠ sc1) (hd2 : dst ≠ sc2)
    (hs0 : src ≠ sc0) (hs1 : src ≠ sc1) :
    (emitReduceBarrett st dst src (fun {_} s => .ret (s.cur dst))).denote V
      = bbBarrett (slotVal st V src) := by
  unfold emitReduceBarrett
  rw [emitConst_denote, emitBin_denote, emitConst_denote, emitBin_denote,
      emitConst_denote, emitBin_denote, emitConst_denote, emitBin_denote,
      emitBin_denote, emitCsub_denote_ret _ _ dst dst hd0 hd1 hd2]
  simp only [slotVal, headVar, JasminBinOp.apply, ite_true, ite_false, hs0, hs1,
    show (sc1 : Fin 25) ≠ sc0 from by decide,
    here_lookup, there_lookup]
  rfl

/-- **Continuation-general `emitReduceBarrett` step.** Running the block equals
    running `k` on a post-state whose `dst` slot reads `bbBarrett (slotVal st V src)`. -/
theorem emitReduceBarrett_denote_step {Γ : Ctxt jasminDialect}
    (st : BState Γ) (dst src : Fin 25) (k : Cont r64) (V : Ctxt.Valuation Γ)
    (hd0 : dst ≠ sc0) (hd1 : dst ≠ sc1) (hd2 : dst ≠ sc2)
    (hs0 : src ≠ sc0) (hs1 : src ≠ sc1) :
    ∃ (Γ' : Ctxt jasminDialect) (st' : BState Γ') (V' : Ctxt.Valuation Γ'),
      (emitReduceBarrett st dst src k).denote V = (k st').denote V'
        ∧ slotVal st' V' dst = bbBarrett (slotVal st V src) := by
  refine ⟨_, _, _, rfl, ?_⟩
  exact emitReduceBarrett_denote_ret st V dst src hd0 hd1 hd2 hs0 hs1

/-- **`emitMulBarrett` computes `bbMul` at `dst`** (read by a `ret dst`
    continuation) on reduced inputs, when `dst` is distinct from the scratch
    slots and `a`, `b` are distinct from `dst`. -/
theorem emitMulBarrett_denote_ret {Γ : Ctxt jasminDialect}
    (st : BState Γ) (V : Ctxt.Valuation Γ) (dst a b : Fin 25)
    (hd0 : dst ≠ sc0) (hd1 : dst ≠ sc1) (hd2 : dst ≠ sc2)
    (_ha : a ≠ dst) (_hb : b ≠ dst)
    (hav : (slotVal st V a).toNat < 2013265921)
    (hbv : (slotVal st V b).toNat < 2013265921) :
    (emitMulBarrett st dst a b (fun {_} s => .ret (s.cur dst))).denote V
      = bbMul (slotVal st V a) (slotVal st V b) := by
  unfold emitMulBarrett
  rw [emitBin_denote, emitReduceBarrett_denote_ret _ _ dst dst hd0 hd1 hd2 hd0 hd1,
    slotVal_step, ite_eq_left rfl]
  exact bbBarrett_mul_eq_bbMul _ _ hav hbv

end CatCrypt.Crypto.SecureCompilation.VIR.BabyBearBarrettBlock
