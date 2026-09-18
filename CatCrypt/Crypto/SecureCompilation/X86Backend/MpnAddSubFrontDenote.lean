/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit

/-!
# The runtime-trip `mpn_add_n` / `mpn_sub_n` loops against their word model

`MpnLoopFrontEmit.addRtProgOpt` / `subRtProgOpt` are the front-compiled runtime-trip
loops behind `mpn_add_n_loop_owned` / `mpn_sub_n_loop_owned`. Their loop-carried
value is a scalar — the carry (add) or the borrow (sub) — and the output array is
a loop invariant written by `RArrStore`.

This module states the word model of both loops and proves their value
invariants, runs each source limb body symbolically through `semScalar` from the
canonical per-trip entry state, and identifies the compiled program's denotation
with the carry (borrow) fold.

The per-limb add step is the two-stage half-add of `MpnAddCarryFrontPrototype`;
its evaluation is the `adc` form `(x + y + c, bSltu (x + y) x + bSltu (x + y + c)
(x + y))` of `MultiLimbKernel.addLimbs`, through `halfCarryW_eq`. The per-limb
sub step is that add step on `(x, ~y)` with carry-in `1 - bw`, and borrow-out
`1 - carry`.

## Scope of the denotation

`ComL.denote` of a scalar-accumulator loop returns the accumulator only. The
output array is an invariant of the loop node, so the trip's `RArrStore` is not
part of the value the denotation returns. The theorems at the denotation are
therefore stated at the returned carry (borrow): `addRtProg_val` /
`subRtProg_val`. The output limbs are pinned at the source level: the per-trip
runs `addLimbBody_run` / `subLimbBody_run` show that trip `t` writes the word
model's limb `t` into `out`, and the word-model folds `addFold` / `subFold`
thread the written array through the invariants `addFold_val` / `subFold_val`.

## Main results

* `addFold_val` / `subFold_val` — for every trip count `k ≤ NR`:
  `bignumVal out[0..k) + carry_k · 2^(64k) = bignumVal a[0..k) + bignumVal b[0..k) + c₀`
  and `bignumVal out[0..k) + bignumVal b[0..k) + bw₀ = bignumVal a[0..k) + bw_k · 2^(64k)`,
  with the carry (borrow) in `{0, 1}`.
* `addLimbBody_run` / `subLimbBody_run` — the per-trip `semScalar` runs.
* `addRtProg_fold` / `subRtProg_fold` — the compiled programs' denotations are the
  carry (borrow) folds, with no front-compilation hypothesis.
* `addRtProg_val` / `subRtProg_val` — the returned carry is
  `(bignumVal a[0..n) + bignumVal b[0..n) + c₀) / 2^(64n)`, and the returned
  borrow is `1` exactly when `bignumVal a[0..n) < bignumVal b[0..n) + bw₀`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubFrontDenote

open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu bSltu_eq)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
  (bignumVal bignumVal_snoc bignumVal_lt adc_toNat adc_carry_le)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (cells cells_succ cells_length memGetDyn_memSetDyn_self)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit (cells_setDyn_of_le)

/-! ## 1. The word model -/

/-- The half-add carry word `((x >>> 1) + (y >>> 1) + ((x &&& y) &&& 1)) >>> 63`, the
    evaluation of `MpnAddCarryFrontPrototype.halfCarry`. -/
def halfCarryW (x y : BitVec 64) : BitVec 64 :=
  ((x >>> 1) + (y >>> 1) + ((x &&& y) &&& 1#64)) >>> 63

/-- The half-add carry word is the carry-out `bSltu (x + y) x` of `x + y`. -/
theorem halfCarryW_eq (x y : BitVec 64) : halfCarryW x y = bSltu (x + y) x := by
  unfold halfCarryW bSltu
  bv_decide

/-- One limb of the add chain: the sum word `x + y + c` and the carry-out. -/
def addLimbW (x y c : BitVec 64) : BitVec 64 × BitVec 64 :=
  (x + y + c, bSltu (x + y) x + bSltu (x + y + c) (x + y))

/-- One limb of the sub chain: the add limb of `(x, ~y)` with carry-in `bw ^^^ 1`
    (`= 1 - bw` for `bw ∈ {0, 1}`); the borrow-out is the complemented carry. -/
def subLimbW (x y bw : BitVec 64) : BitVec 64 × BitVec 64 :=
  ((addLimbW x (~~~y) (bw ^^^ 1#64)).1, (addLimbW x (~~~y) (bw ^^^ 1#64)).2 ^^^ 1#64)

/-- `bw ^^^ 1` is `1 - bw` on a `{0, 1}` word. -/
theorem xor_one_toNat (w : BitVec 64) (h : w.toNat ≤ 1) :
    (w ^^^ 1#64).toNat = 1 - w.toNat := by
  have hw : w = 0#64 ∨ w = 1#64 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simpa using h0))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simpa using h1))
  rcases hw with rfl | rfl <;> decide

/-- The limb identity of the add step: `sum + carry · 2^64 = x + y + c`, with the
    carry in `{0, 1}` when `c` is. -/
theorem addLimbW_val (x y c : BitVec 64) (hc : c.toNat ≤ 1) :
    (addLimbW x y c).1.toNat + (addLimbW x y c).2.toNat * 2 ^ 64
        = x.toNat + y.toNat + c.toNat
      ∧ (addLimbW x y c).2.toNat ≤ 1 :=
  ⟨adc_toNat x y c, adc_carry_le x y c hc⟩

/-- The limb identity of the sub step: `diff + y + bw = x + bw' · 2^64`, with the
    borrow in `{0, 1}` when `bw` is. -/
theorem subLimbW_val (x y bw : BitVec 64) (hbw : bw.toNat ≤ 1) :
    (subLimbW x y bw).1.toNat + y.toNat + bw.toNat
        = x.toNat + (subLimbW x y bw).2.toNat * 2 ^ 64
      ∧ (subLimbW x y bw).2.toNat ≤ 1 := by
  have hcx : (bw ^^^ 1#64).toNat = 1 - bw.toNat := xor_one_toNat bw hbw
  have hcx1 : (bw ^^^ 1#64).toNat ≤ 1 := by omega
  obtain ⟨hv, hc⟩ := addLimbW_val x (~~~y) (bw ^^^ 1#64) hcx1
  have hco := xor_one_toNat _ hc
  have hny : (~~~y).toNat = 2 ^ 64 - 1 - y.toNat := BitVec.toNat_not
  have hy := y.isLt
  simp only [subLimbW]
  refine ⟨?_, by omega⟩
  rw [hco]
  rw [hcx, hny] at hv
  generalize (addLimbW x (~~~y) (bw ^^^ 1#64)).2.toNat = C at hv hc ⊢
  generalize (addLimbW x (~~~y) (bw ^^^ 1#64)).1.toNat = S at hv ⊢
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> omega

/-- The add loop's per-trip step on the `(out, carry)` state: write the sum limb
    of `a[t] + b[t] + carry` at cell `t` and carry the carry-out. -/
def addStep {NA NB NR : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (st : (Fin NR → BitVec 64) × BitVec 64) (t : Nat) :
    (Fin NR → BitVec 64) × BitVec 64 :=
  (memSetDyn st.1 t (addLimbW (memGetDyn ap t) (memGetDyn bp t) st.2).1,
   (addLimbW (memGetDyn ap t) (memGetDyn bp t) st.2).2)

/-- The add loop's word model: `k` trips of `addStep` from `st₀`. -/
def addFold {NA NB NR : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (k : Nat) (st₀ : (Fin NR → BitVec 64) × BitVec 64) :
    (Fin NR → BitVec 64) × BitVec 64 :=
  (List.range k).foldl (addStep ap bp) st₀

/-- The sub loop's per-trip step on the `(out, borrow)` state: write the
    difference limb of `a[t] - b[t] - borrow` at cell `t` and carry the
    borrow-out. -/
def subStep {NA NB NR : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (st : (Fin NR → BitVec 64) × BitVec 64) (t : Nat) :
    (Fin NR → BitVec 64) × BitVec 64 :=
  (memSetDyn st.1 t (subLimbW (memGetDyn ap t) (memGetDyn bp t) st.2).1,
   (subLimbW (memGetDyn ap t) (memGetDyn bp t) st.2).2)

/-- The sub loop's word model: `k` trips of `subStep` from `st₀`. -/
def subFold {NA NB NR : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (k : Nat) (st₀ : (Fin NR → BitVec 64) × BitVec 64) :
    (Fin NR → BitVec 64) × BitVec 64 :=
  (List.range k).foldl (subStep ap bp) st₀

/-- The add loop's carry fold: the carry component of `addFold`, which does not
    read the output array. -/
def addCarryFold {NA NB : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (k : Nat) (c₀ : BitVec 64) : BitVec 64 :=
  (List.range k).foldl (fun c t => (addLimbW (memGetDyn ap t) (memGetDyn bp t) c).2) c₀

/-- The sub loop's borrow fold: the borrow component of `subFold`. -/
def subBorrowFold {NA NB : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (k : Nat) (bw₀ : BitVec 64) : BitVec 64 :=
  (List.range k).foldl (fun c t => (subLimbW (memGetDyn ap t) (memGetDyn bp t) c).2) bw₀

theorem addFold_succ {NA NB NR : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (k : Nat) (st₀ : (Fin NR → BitVec 64) × BitVec 64) :
    addFold ap bp (k + 1) st₀ = addStep ap bp (addFold ap bp k st₀) k := by
  simp [addFold, List.range_succ, List.foldl_append]

theorem subFold_succ {NA NB NR : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (k : Nat) (st₀ : (Fin NR → BitVec 64) × BitVec 64) :
    subFold ap bp (k + 1) st₀ = subStep ap bp (subFold ap bp k st₀) k := by
  simp [subFold, List.range_succ, List.foldl_append]

/-- The carry component of the add word model is the carry fold. -/
theorem addFold_snd {NA NB NR : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (k : Nat) (o : Fin NR → BitVec 64) (c₀ : BitVec 64) :
    (addFold ap bp k (o, c₀)).2 = addCarryFold ap bp k c₀ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [addFold_succ]
      simp only [addStep, addCarryFold, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [ih]
      rfl

/-- The borrow component of the sub word model is the borrow fold. -/
theorem subFold_snd {NA NB NR : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (k : Nat) (o : Fin NR → BitVec 64) (bw₀ : BitVec 64) :
    (subFold ap bp k (o, bw₀)).2 = subBorrowFold ap bp k bw₀ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [subFold_succ]
      simp only [subStep, subBorrowFold, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [ih]
      rfl

/-- Writing cell `k` and reading the first `k + 1` cells appends the written word. -/
theorem cells_setDyn_succ {N : Nat} (o : Fin N → BitVec 64) (k : Nat) (v : BitVec 64)
    (hk : k < N) : cells (memSetDyn o k v) (k + 1) = cells o k ++ [v] := by
  rw [cells_succ, cells_setDyn_of_le o k k v le_rfl hk, memGetDyn_memSetDyn_self o k v hk]

/-- **The add loop invariant.** After `k ≤ NR` trips from carry-in `c₀ ∈ {0, 1}`,
    the written cells plus the carry scaled by `2^(64k)` are the sum of the two
    operand prefixes plus `c₀`, and the carry is in `{0, 1}`. -/
theorem addFold_val {NA NB NR : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (o : Fin NR → BitVec 64) (c₀ : BitVec 64) (hc₀ : c₀.toNat ≤ 1) :
    ∀ k, k ≤ NR →
      bignumVal (cells (addFold ap bp k (o, c₀)).1 k)
          + (addFold ap bp k (o, c₀)).2.toNat * (2 ^ 64) ^ k
        = bignumVal (cells ap k) + bignumVal (cells bp k) + c₀.toNat
      ∧ (addFold ap bp k (o, c₀)).2.toNat ≤ 1 := by
  intro k
  induction k with
  | zero => intro _; simp [addFold, cells, bignumVal, hc₀]
  | succ k ih =>
      intro hk
      obtain ⟨hv, hc⟩ := ih (by omega)
      rw [addFold_succ]
      obtain ⟨hl, hl1⟩ := addLimbW_val (memGetDyn ap k) (memGetDyn bp k)
        (addFold ap bp k (o, c₀)).2 hc
      refine ⟨?_, hl1⟩
      simp only [addStep]
      rw [cells_setDyn_succ _ _ _ (by omega), bignumVal_snoc, cells_length,
        cells_succ ap, cells_succ bp, bignumVal_snoc, bignumVal_snoc, cells_length,
        cells_length, pow_succ ((2 : Nat) ^ 64) k]
      generalize ((2 : Nat) ^ 64) ^ k = P at hv ⊢
      generalize (2 : Nat) ^ 64 = B at hl ⊢
      generalize (addFold ap bp k (o, c₀)).2.toNat = C at hv hl ⊢
      linear_combination hv + P * hl

/-- **The sub loop invariant.** After `k ≤ NR` trips from borrow-in `bw₀ ∈ {0, 1}`,
    the written cells plus the subtrahend prefix plus `bw₀` are the minuend prefix
    plus the borrow scaled by `2^(64k)`, and the borrow is in `{0, 1}`. -/
theorem subFold_val {NA NB NR : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (o : Fin NR → BitVec 64) (bw₀ : BitVec 64) (hbw₀ : bw₀.toNat ≤ 1) :
    ∀ k, k ≤ NR →
      bignumVal (cells (subFold ap bp k (o, bw₀)).1 k) + bignumVal (cells bp k) + bw₀.toNat
        = bignumVal (cells ap k) + (subFold ap bp k (o, bw₀)).2.toNat * (2 ^ 64) ^ k
      ∧ (subFold ap bp k (o, bw₀)).2.toNat ≤ 1 := by
  intro k
  induction k with
  | zero => intro _; simp [subFold, cells, bignumVal, hbw₀]
  | succ k ih =>
      intro hk
      obtain ⟨hv, hc⟩ := ih (by omega)
      rw [subFold_succ]
      obtain ⟨hl, hl1⟩ := subLimbW_val (memGetDyn ap k) (memGetDyn bp k)
        (subFold ap bp k (o, bw₀)).2 hc
      refine ⟨?_, hl1⟩
      simp only [subStep]
      rw [cells_setDyn_succ _ _ _ (by omega), bignumVal_snoc, cells_length,
        cells_succ ap, cells_succ bp, bignumVal_snoc, bignumVal_snoc, cells_length,
        cells_length, pow_succ ((2 : Nat) ^ 64) k]
      generalize ((2 : Nat) ^ 64) ^ k = P at hv ⊢
      generalize (2 : Nat) ^ 64 = B at hl ⊢
      generalize (subFold ap bp k (o, bw₀)).2.toNat = C at hv hl ⊢
      linear_combination hv + P * hl

/-! ## 2. The source limb bodies: evaluation identities and lowering progress -/

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (SEnvScalar ConsistentS semScalar IsCoveredS IsCoveredSCtl srcClean isTmpName
   envReadU64 envReader semLowerSExpr binNode consistentS_empty)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (tmpName)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
  (rolledForLoopNRt_denote)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontLoopBodyStepC
  (consistentS_bind frontLoopBodyJ_denote_foldl)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (upd_ne upd_self envReadU64_of_bound envReader_of_bound envReadU64_upd_ne
   envReadU64_upd_self semScalar_arrLoad semScalar_arrStore semScalar_setExpr_run)
open CatCrypt.Crypto.SecureCompilation.Ascent (notTmp_of_short)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote
  (ne_tmp_of_short seqAll_step lower_add_vv)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype
  (halfCarry mask64 N AN r64 Γbody vmBody addBodyLowCT)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
  (ΓouterCarry addRtProgOpt subRtProgOpt subBodyLowCT vmBodySub)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-- The prototype's sequencing helper is `MpnMul1FrontEmit.seqAll`. -/
theorem seqAll_proto_eq :
    MpnAddCarryFrontPrototype.seqAll = MpnMul1FrontEmit.seqAll := by
  funext l
  induction l with
  | nil => rfl
  | cons c cs ih =>
      cases cs with
      | nil => rfl
      | cons d ds =>
          simp only [MpnAddCarryFrontPrototype.seqAll, MpnMul1FrontEmit.seqAll] at ih ⊢
          rw [ih]

/-- The `halfCarry` expression evaluates to the carry-out `bSltu (x + y) x`. -/
theorem halfCarry_evalBV (β : String → BitVec 64) (x y : String) :
    (halfCarry x y).evalBV β = bSltu (β x + β y) (β x) :=
  halfCarryW_eq (β x) (β y)

/-- The `mask64` word is all-ones. -/
theorem ofNat_mask64 : BitVec.ofNat 64 mask64 = BitVec.allOnes 64 := by decide

/-- Masking with `mask64` is the identity on the wrapping-`u64` evaluator. -/
theorem mask_evalBV (β : String → BitVec 64) (e : SExpr) :
    (SExpr.SAnd e (.SLit mask64)).evalBV β = e.evalBV β := by
  simp only [SExpr.evalBV, ofNat_mask64, BitVec.and_allOnes]

/-- XOR with `mask64` is bitwise complement on the wrapping-`u64` evaluator. -/
theorem notMask_evalBV (β : String → BitVec 64) (e : SExpr) :
    (SExpr.SXor e (.SLit mask64)).evalBV β = ~~~ e.evalBV β := by
  simp only [SExpr.evalBV, ofNat_mask64, BitVec.xor_allOnes]

/-- Progress of a bare variable read. -/
theorem lower_var {env : SEnvScalar} {x : String} {wx : BitVec 64}
    (hx : envReadU64 env x = some wx) :
    (semLowerSExpr env 0 (.SVar x)).isSome := by
  simp only [semLowerSExpr, hx]
  rfl

/-- Progress of the half-add carry expression over two short names. -/
theorem lower_hc {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy)
    (hxl : x.length < 4) (hyl : y.length < 4) :
    (semLowerSExpr env 0 (halfCarry x y)).isSome := by
  simp (disch := first | decide | exact ne_tmp_of_short hxl _ | exact ne_tmp_of_short hyl _)
    only [halfCarry, semLowerSExpr, binNode, hx, hy, envReadU64_upd_self, envReadU64_upd_ne]
  rfl

/-- Progress of the masked sum `(x + y) & mask64` over two short names. -/
theorem lower_addMask {env : SEnvScalar} {x y : String} {wx wy : BitVec 64}
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy) :
    (semLowerSExpr env 0 (.SAnd (.SAdd (.SVar x) (.SVar y)) (.SLit mask64))).isSome := by
  simp (disch := decide)
    only [semLowerSExpr, binNode, hx, hy, envReadU64_upd_self, envReadU64_upd_ne]
  rfl

/-- Progress of `x ^ lit` over a short name. -/
theorem lower_xorLit {env : SEnvScalar} {x : String} {wx : BitVec 64} (L : Nat)
    (hx : envReadU64 env x = some wx) (hxl : x.length < 4) :
    (semLowerSExpr env 0 (.SXor (.SVar x) (.SLit L))).isSome := by
  simp (disch := first | decide | exact ne_tmp_of_short hxl _)
    only [semLowerSExpr, binNode, hx, envReadU64_upd_self, envReadU64_upd_ne]
  rfl

/-- Progress of `(x + y) ^ lit` over two names. -/
theorem lower_addXorLit {env : SEnvScalar} {x y : String} {wx wy : BitVec 64} (L : Nat)
    (hx : envReadU64 env x = some wx) (hy : envReadU64 env y = some wy) :
    (semLowerSExpr env 0 (.SXor (.SAdd (.SVar x) (.SVar y)) (.SLit L))).isSome := by
  simp (disch := decide)
    only [semLowerSExpr, binNode, hx, hy, envReadU64_upd_self, envReadU64_upd_ne]
  rfl

/-! ## 3. Name freshness and coverage -/

theorem nt_idx : ¬ isTmpName "idx" := notTmp_of_short _ (by decide)
theorem nt_ix : ¬ isTmpName "ix" := notTmp_of_short _ (by decide)
theorem nt_ai : ¬ isTmpName "ai" := notTmp_of_short _ (by decide)
theorem nt_bi : ¬ isTmpName "bi" := notTmp_of_short _ (by decide)
theorem nt_nb : ¬ isTmpName "nb" := notTmp_of_short _ (by decide)
theorem nt_cx : ¬ isTmpName "cx" := notTmp_of_short _ (by decide)
theorem nt_c1 : ¬ isTmpName "c1" := notTmp_of_short _ (by decide)
theorem nt_c2 : ¬ isTmpName "c2" := notTmp_of_short _ (by decide)
theorem nt_s1 : ¬ isTmpName "s1" := notTmp_of_short _ (by decide)
theorem nt_sum : ¬ isTmpName "sum" := notTmp_of_short _ (by decide)
theorem nt_df : ¬ isTmpName "df" := notTmp_of_short _ (by decide)
theorem nt_cy : ¬ isTmpName "cy" := notTmp_of_short _ (by decide)
theorem nt_bw : ¬ isTmpName "bw" := notTmp_of_short _ (by decide)
theorem nt_out : ¬ isTmpName "out" := notTmp_of_short _ (by decide)

/-- Literal bound for `mask64`. -/
theorem hmask : mask64 < 2 ^ 64 := by decide

/-- `halfCarry` over two non-temporary names is `srcClean`. -/
theorem srcClean_halfCarry {x y : String} (hx : ¬ isTmpName x) (hy : ¬ isTmpName y) :
    srcClean (halfCarry x y) :=
  ⟨⟨⟨⟨hx, (by decide : (1 : Nat) < 2 ^ 64)⟩, ⟨hy, (by decide : (1 : Nat) < 2 ^ 64)⟩⟩,
    ⟨⟨hx, hy⟩, (by decide : (1 : Nat) < 2 ^ 64)⟩⟩, (by decide : (63 : Nat) < 2 ^ 64)⟩

/-- The `mpn_add_n` limb body is covered straight-line `LowCT`. -/
theorem addBody_coveredS : IsCoveredS addBodyLowCT :=
  .rSeq (.rScalarSetExpr _ _ nt_idx)
   (.rSeq (.rArrLoad _ _ _)
    (.rSeq (.rArrLoad _ _ _)
     (.rSeq (.rScalarSetExpr _ _ (srcClean_halfCarry nt_ai nt_bi))
      (.rSeq (.rScalarSetExpr _ _ ⟨⟨nt_ai, nt_bi⟩, hmask⟩)
       (.rSeq (.rScalarSetExpr _ _ (srcClean_halfCarry nt_s1 nt_cy))
        (.rSeq (.rScalarSetExpr _ _ ⟨⟨nt_s1, nt_cy⟩, hmask⟩)
         (.rSeq (.rArrStore _ _ _)
          (.rScalarSetExpr _ _ ⟨nt_c1, nt_c2⟩))))))))

theorem addBody_covered : IsCoveredSCtl addBodyLowCT := .ofStraight addBody_coveredS

/-- The `mpn_sub_n` limb body is covered straight-line `LowCT`. -/
theorem subBody_coveredS : IsCoveredS subBodyLowCT :=
  .rSeq (.rScalarSetExpr _ _ nt_idx)
   (.rSeq (.rArrLoad _ _ _)
    (.rSeq (.rArrLoad _ _ _)
     (.rSeq (.rScalarSetExpr _ _ ⟨nt_bi, hmask⟩)
      (.rSeq (.rScalarSetExpr _ _ ⟨nt_bw, (by decide : (1 : Nat) < 2 ^ 64)⟩)
       (.rSeq (.rScalarSetExpr _ _ (srcClean_halfCarry nt_ai nt_nb))
        (.rSeq (.rScalarSetExpr _ _ ⟨⟨nt_ai, nt_nb⟩, hmask⟩)
         (.rSeq (.rScalarSetExpr _ _ (srcClean_halfCarry nt_s1 nt_cx))
          (.rSeq (.rScalarSetExpr _ _ ⟨⟨nt_s1, nt_cx⟩, hmask⟩)
           (.rSeq (.rArrStore _ _ _)
            (.rScalarSetExpr _ _ ⟨⟨nt_c1, nt_c2⟩, (by decide : (1 : Nat) < 2 ^ 64)⟩))))))))))

theorem subBody_covered : IsCoveredSCtl subBodyLowCT := .ofStraight subBody_coveredS

/-! ## 4. The front-compiled bodies -/

/-- The front accepts the `mpn_add_n` limb body. -/
theorem addFrontOk :
    (frontLoopBodyJ (accCTy := .sword 64) vmBody "cy" addBodyLowCT).isSome := by
  rfl

/-- The front accepts the `mpn_sub_n` limb body. -/
theorem subFrontOk :
    (frontLoopBodyJ (accCTy := .sword 64) vmBodySub "bw" subBodyLowCT).isSome := by
  rfl

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the
    `mpn_add_n` limb body. -/
def addUpdate : Com jasminDialect (mapCtx Γbody) (mapTy (CryptoTy.sword 64)) :=
  (frontLoopBodyJ (accCTy := .sword 64) vmBody "cy" addBodyLowCT).get addFrontOk

theorem addUpdate_eq :
    frontLoopBodyJ (accCTy := .sword 64) vmBody "cy" addBodyLowCT = some addUpdate :=
  (Option.some_get addFrontOk).symm

/-- The `JLoopBodyN.update`-shaped jasmin program the front emits for the
    `mpn_sub_n` limb body. -/
def subUpdate : Com jasminDialect (mapCtx Γbody) (mapTy (CryptoTy.sword 64)) :=
  (frontLoopBodyJ (accCTy := .sword 64) vmBodySub "bw" subBodyLowCT).get subFrontOk

theorem subUpdate_eq :
    frontLoopBodyJ (accCTy := .sword 64) vmBodySub "bw" subBodyLowCT = some subUpdate :=
  (Option.some_get subFrontOk).symm

/-! ## 5. The canonical per-trip entry states -/

/-- The everywhere-unbound environment. -/
def emptyEnv : SEnvScalar := fun _ => none

/-- The canonical entry environment of a carry-family limb body at one trip: the
    output array at `out`, the operands at `b` / `a`, the trip index at `idx`, the
    carry (borrow) at `acc`. -/
def carryEnv (acc : String) (ap bp o : Fin N → BitVec 64) (cy iv : BitVec 64) :
    SEnvScalar :=
  (((((emptyEnv.upd "out" (t := .memref N) o).upd
      "b" (t := .memref N) bp).upd
      "a" (t := .memref N) ap).upd
      "idx" (t := .sword 64) iv).upd acc (t := .sword 64) cy)

theorem consistentS_addEnv (ap bp o : Fin N → BitVec 64) (cy iv : BitVec 64) :
    ConsistentS vmBody (.cons cy (.cons iv (.cons ap (.cons bp (.cons o .nil)))))
      (carryEnv "cy" ap bp o cy iv) :=
  consistentS_bind (consistentS_bind (consistentS_bind (consistentS_bind
    (consistentS_bind consistentS_empty "out" (t := .memref N) o)
    "b" (t := .memref N) bp) "a" (t := .memref N) ap)
    "idx" (t := .sword 64) iv) "cy" (t := .sword 64) cy

theorem consistentS_subEnv (ap bp o : Fin N → BitVec 64) (bw iv : BitVec 64) :
    ConsistentS vmBodySub (.cons bw (.cons iv (.cons ap (.cons bp (.cons o .nil)))))
      (carryEnv "bw" ap bp o bw iv) :=
  consistentS_bind (consistentS_bind (consistentS_bind (consistentS_bind
    (consistentS_bind consistentS_empty "out" (t := .memref N) o)
    "b" (t := .memref N) bp) "a" (t := .memref N) ap)
    "idx" (t := .sword 64) iv) "bw" (t := .sword 64) bw

section EnvReads

variable (acc : String) (ap bp o : Fin N → BitVec 64) (cy iv : BitVec 64)

theorem carryEnv_acc : carryEnv acc ap bp o cy iv acc = some ⟨.sword 64, cy⟩ :=
  upd_self _ _ _

theorem carryEnv_idx (h : "idx" ≠ acc) :
    carryEnv acc ap bp o cy iv "idx" = some ⟨.sword 64, iv⟩ := by
  rw [carryEnv, upd_ne h]; exact upd_self _ _ _

theorem carryEnv_a (h : "a" ≠ acc) :
    carryEnv acc ap bp o cy iv "a" = some ⟨.memref N, ap⟩ := by
  rw [carryEnv, upd_ne h, upd_ne (by decide)]; exact upd_self _ _ _

theorem carryEnv_b (h : "b" ≠ acc) :
    carryEnv acc ap bp o cy iv "b" = some ⟨.memref N, bp⟩ := by
  rw [carryEnv, upd_ne h, upd_ne (by decide), upd_ne (by decide)]; exact upd_self _ _ _

theorem carryEnv_out (h : "out" ≠ acc) :
    carryEnv acc ap bp o cy iv "out" = some ⟨.memref N, o⟩ := by
  rw [carryEnv, upd_ne h, upd_ne (by decide), upd_ne (by decide), upd_ne (by decide)]
  exact upd_self _ _ _

end EnvReads

/-! ## 6. The per-trip runs of the limb bodies -/

/-- **The add limb body computes one `addLimbW` step.** From the canonical entry
    state at trip `t`, the source body's `semScalar` run terminates, leaves the
    carry-out of `a[t] + b[t] + cy` in `cy`, and writes the sum limb at cell `t`
    of `out`. -/
theorem addLimbBody_run (ap bp o : Fin N → BitVec 64) (cy : BitVec 64) (t : Nat)
    (ht : t < 2 ^ 64) :
    ∃ env', semScalar addBodyLowCT (carryEnv "cy" ap bp o cy (BitVec.ofNat 64 t)) = some env'
      ∧ env' "cy" = some ⟨.sword 64, (addLimbW (memGetDyn ap t) (memGetDyn bp t) cy).2⟩
      ∧ env' "out" = some ⟨.memref N,
          memSetDyn o t (addLimbW (memGetDyn ap t) (memGetDyn bp t) cy).1⟩ := by
  set iv : BitVec 64 := BitVec.ofNat 64 t with hivdef
  have hivN : iv.toNat = t := by rw [hivdef, BitVec.toNat_ofNat]; omega
  have hbody : addBodyLowCT = MpnMul1FrontEmit.seqAll
    [ .RScalarSetExpr "ix" (.SVar "idx")
    , .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix"
    , .RArrLoad ⟨"bi", .TU64⟩ ⟨"b", .TBytes (8 * N)⟩ "ix"
    , .RScalarSetExpr "c1" (halfCarry "ai" "bi")
    , .RScalarSetExpr "s1" (.SAnd (.SAdd (.SVar "ai") (.SVar "bi")) (.SLit mask64))
    , .RScalarSetExpr "c2" (halfCarry "s1" "cy")
    , .RScalarSetExpr "sum" (.SAnd (.SAdd (.SVar "s1") (.SVar "cy")) (.SLit mask64))
    , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"sum", .TU64⟩
    , .RScalarSetExpr "cy" (.SAdd (.SVar "c1") (.SVar "c2")) ] := by
    rw [addBodyLowCT, seqAll_proto_eq]
  have h0cy := carryEnv_acc "cy" ap bp o cy iv
  have h0idx := carryEnv_idx "cy" ap bp o cy iv (by decide)
  have h0a := carryEnv_a "cy" ap bp o cy iv (by decide)
  have h0b := carryEnv_b "cy" ap bp o cy iv (by decide)
  have h0out := carryEnv_out "cy" ap bp o cy iv (by decide)
  -- step 1: ix := idx
  obtain ⟨e1, hs1, h1ix, hf1⟩ := semScalar_setExpr_run (y := "ix")
    (lower_var (envReadU64_of_bound h0idx))
  simp only [SExpr.evalBV, envReader_of_bound h0idx] at h1ix
  have h1cy := (hf1 "cy" nt_cy (by decide)).trans h0cy
  have h1a := (hf1 "a" (notTmp_of_short _ (by decide)) (by decide)).trans h0a
  have h1b := (hf1 "b" (notTmp_of_short _ (by decide)) (by decide)).trans h0b
  have h1out := (hf1 "out" nt_out (by decide)).trans h0out
  -- step 2: ai := a[ix]
  obtain ⟨e2, hs2, h2ai, hf2⟩ :=
    semScalar_arrLoad (dstN := "ai") (tw := .TBytes (8 * N)) (idxN := "ix") h1a h1ix
  rw [hivN] at h2ai
  have h2cy := (hf2 "cy" (by decide)).trans h1cy
  have h2b := (hf2 "b" (by decide)).trans h1b
  have h2ix := (hf2 "ix" (by decide)).trans h1ix
  have h2out := (hf2 "out" (by decide)).trans h1out
  -- step 3: bi := b[ix]
  obtain ⟨e3, hs3, h3bi, hf3⟩ :=
    semScalar_arrLoad (dstN := "bi") (tw := .TBytes (8 * N)) (idxN := "ix") h2b h2ix
  rw [hivN] at h3bi
  have h3cy := (hf3 "cy" (by decide)).trans h2cy
  have h3ix := (hf3 "ix" (by decide)).trans h2ix
  have h3out := (hf3 "out" (by decide)).trans h2out
  have h3ai := (hf3 "ai" (by decide)).trans h2ai
  -- step 4: c1 := halfCarry ai bi
  obtain ⟨e4, hs4, h4c1, hf4⟩ := semScalar_setExpr_run (y := "c1")
    (lower_hc (envReadU64_of_bound h3ai) (envReadU64_of_bound h3bi) (by decide) (by decide))
  rw [halfCarry_evalBV, envReader_of_bound h3ai, envReader_of_bound h3bi] at h4c1
  have h4cy := (hf4 "cy" nt_cy (by decide)).trans h3cy
  have h4ix := (hf4 "ix" nt_ix (by decide)).trans h3ix
  have h4out := (hf4 "out" nt_out (by decide)).trans h3out
  have h4ai := (hf4 "ai" nt_ai (by decide)).trans h3ai
  have h4bi := (hf4 "bi" nt_bi (by decide)).trans h3bi
  -- step 5: s1 := (ai + bi) & mask64
  obtain ⟨e5, hs5, h5s1, hf5⟩ := semScalar_setExpr_run (y := "s1")
    (lower_addMask (envReadU64_of_bound h4ai) (envReadU64_of_bound h4bi))
  rw [mask_evalBV] at h5s1
  simp only [SExpr.evalBV, envReader_of_bound h4ai, envReader_of_bound h4bi] at h5s1
  have h5cy := (hf5 "cy" nt_cy (by decide)).trans h4cy
  have h5ix := (hf5 "ix" nt_ix (by decide)).trans h4ix
  have h5out := (hf5 "out" nt_out (by decide)).trans h4out
  have h5c1 := (hf5 "c1" nt_c1 (by decide)).trans h4c1
  -- step 6: c2 := halfCarry s1 cy
  obtain ⟨e6, hs6, h6c2, hf6⟩ := semScalar_setExpr_run (y := "c2")
    (lower_hc (envReadU64_of_bound h5s1) (envReadU64_of_bound h5cy) (by decide) (by decide))
  rw [halfCarry_evalBV, envReader_of_bound h5s1, envReader_of_bound h5cy] at h6c2
  have h6cy := (hf6 "cy" nt_cy (by decide)).trans h5cy
  have h6ix := (hf6 "ix" nt_ix (by decide)).trans h5ix
  have h6out := (hf6 "out" nt_out (by decide)).trans h5out
  have h6c1 := (hf6 "c1" nt_c1 (by decide)).trans h5c1
  have h6s1 := (hf6 "s1" nt_s1 (by decide)).trans h5s1
  -- step 7: sum := (s1 + cy) & mask64
  obtain ⟨e7, hs7, h7sum, hf7⟩ := semScalar_setExpr_run (y := "sum")
    (lower_addMask (envReadU64_of_bound h6s1) (envReadU64_of_bound h6cy))
  rw [mask_evalBV] at h7sum
  simp only [SExpr.evalBV, envReader_of_bound h6s1, envReader_of_bound h6cy] at h7sum
  have h7ix := (hf7 "ix" nt_ix (by decide)).trans h6ix
  have h7out := (hf7 "out" nt_out (by decide)).trans h6out
  have h7c1 := (hf7 "c1" nt_c1 (by decide)).trans h6c1
  have h7c2 := (hf7 "c2" nt_c2 (by decide)).trans h6c2
  -- step 8: out[ix] := sum
  obtain ⟨e8, hs8, h8out, hf8⟩ :=
    semScalar_arrStore (fw := 8 * N) h7out h7ix h7sum
  rw [hivN] at h8out
  have h8c1 := (hf8 "c1" (by decide)).trans h7c1
  have h8c2 := (hf8 "c2" (by decide)).trans h7c2
  -- step 9: cy := c1 + c2
  obtain ⟨e9, hs9, h9cy, hf9⟩ := semScalar_setExpr_run (y := "cy")
    (lower_add_vv (envReadU64_of_bound h8c1) (envReadU64_of_bound h8c2))
  simp only [SExpr.evalBV, envReader_of_bound h8c1, envReader_of_bound h8c2] at h9cy
  have h9out := (hf9 "out" nt_out (by decide)).trans h8out
  refine ⟨e9, ?_, ?_, ?_⟩
  · rw [hbody, seqAll_step hs1, seqAll_step hs2, seqAll_step hs3, seqAll_step hs4,
      seqAll_step hs5, seqAll_step hs6, seqAll_step hs7, seqAll_step hs8]
    exact hs9
  · rw [h9cy]; rfl
  · rw [h9out]; rfl

/-- **The sub limb body computes one `subLimbW` step.** From the canonical entry
    state at trip `t`, the source body's `semScalar` run terminates, leaves the
    borrow-out of `a[t] - b[t] - bw` in `bw`, and writes the difference limb at
    cell `t` of `out`. -/
theorem subLimbBody_run (ap bp o : Fin N → BitVec 64) (bw : BitVec 64) (t : Nat)
    (ht : t < 2 ^ 64) :
    ∃ env', semScalar subBodyLowCT (carryEnv "bw" ap bp o bw (BitVec.ofNat 64 t)) = some env'
      ∧ env' "bw" = some ⟨.sword 64, (subLimbW (memGetDyn ap t) (memGetDyn bp t) bw).2⟩
      ∧ env' "out" = some ⟨.memref N,
          memSetDyn o t (subLimbW (memGetDyn ap t) (memGetDyn bp t) bw).1⟩ := by
  set iv : BitVec 64 := BitVec.ofNat 64 t with hivdef
  have hivN : iv.toNat = t := by rw [hivdef, BitVec.toNat_ofNat]; omega
  have hbody : subBodyLowCT = MpnMul1FrontEmit.seqAll
    [ .RScalarSetExpr "ix" (.SVar "idx")
    , .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix"
    , .RArrLoad ⟨"bi", .TU64⟩ ⟨"b", .TBytes (8 * N)⟩ "ix"
    , .RScalarSetExpr "nb" (.SXor (.SVar "bi") (.SLit mask64))
    , .RScalarSetExpr "cx" (.SXor (.SVar "bw") (.SLit 1))
    , .RScalarSetExpr "c1" (halfCarry "ai" "nb")
    , .RScalarSetExpr "s1" (.SAnd (.SAdd (.SVar "ai") (.SVar "nb")) (.SLit mask64))
    , .RScalarSetExpr "c2" (halfCarry "s1" "cx")
    , .RScalarSetExpr "df" (.SAnd (.SAdd (.SVar "s1") (.SVar "cx")) (.SLit mask64))
    , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"df", .TU64⟩
    , .RScalarSetExpr "bw" (.SXor (.SAdd (.SVar "c1") (.SVar "c2")) (.SLit 1)) ] := by
    rw [subBodyLowCT, seqAll_proto_eq]
  have h0bw := carryEnv_acc "bw" ap bp o bw iv
  have h0idx := carryEnv_idx "bw" ap bp o bw iv (by decide)
  have h0a := carryEnv_a "bw" ap bp o bw iv (by decide)
  have h0b := carryEnv_b "bw" ap bp o bw iv (by decide)
  have h0out := carryEnv_out "bw" ap bp o bw iv (by decide)
  -- step 1: ix := idx
  obtain ⟨e1, hs1, h1ix, hf1⟩ := semScalar_setExpr_run (y := "ix")
    (lower_var (envReadU64_of_bound h0idx))
  simp only [SExpr.evalBV, envReader_of_bound h0idx] at h1ix
  have h1bw := (hf1 "bw" nt_bw (by decide)).trans h0bw
  have h1a := (hf1 "a" (notTmp_of_short _ (by decide)) (by decide)).trans h0a
  have h1b := (hf1 "b" (notTmp_of_short _ (by decide)) (by decide)).trans h0b
  have h1out := (hf1 "out" nt_out (by decide)).trans h0out
  -- step 2: ai := a[ix]
  obtain ⟨e2, hs2, h2ai, hf2⟩ :=
    semScalar_arrLoad (dstN := "ai") (tw := .TBytes (8 * N)) (idxN := "ix") h1a h1ix
  rw [hivN] at h2ai
  have h2bw := (hf2 "bw" (by decide)).trans h1bw
  have h2b := (hf2 "b" (by decide)).trans h1b
  have h2ix := (hf2 "ix" (by decide)).trans h1ix
  have h2out := (hf2 "out" (by decide)).trans h1out
  -- step 3: bi := b[ix]
  obtain ⟨e3, hs3, h3bi, hf3⟩ :=
    semScalar_arrLoad (dstN := "bi") (tw := .TBytes (8 * N)) (idxN := "ix") h2b h2ix
  rw [hivN] at h3bi
  have h3bw := (hf3 "bw" (by decide)).trans h2bw
  have h3ix := (hf3 "ix" (by decide)).trans h2ix
  have h3out := (hf3 "out" (by decide)).trans h2out
  have h3ai := (hf3 "ai" (by decide)).trans h2ai
  -- step 4: nb := bi ^ mask64
  obtain ⟨e4, hs4, h4nb, hf4⟩ := semScalar_setExpr_run (y := "nb")
    (lower_xorLit mask64 (envReadU64_of_bound h3bi) (by decide))
  rw [notMask_evalBV] at h4nb
  simp only [SExpr.evalBV, envReader_of_bound h3bi] at h4nb
  have h4bw := (hf4 "bw" nt_bw (by decide)).trans h3bw
  have h4ix := (hf4 "ix" nt_ix (by decide)).trans h3ix
  have h4out := (hf4 "out" nt_out (by decide)).trans h3out
  have h4ai := (hf4 "ai" nt_ai (by decide)).trans h3ai
  -- step 5: cx := bw ^ 1
  obtain ⟨e5, hs5, h5cx, hf5⟩ := semScalar_setExpr_run (y := "cx")
    (lower_xorLit 1 (envReadU64_of_bound h4bw) (by decide))
  simp only [SExpr.evalBV, envReader_of_bound h4bw] at h5cx
  have h5ix := (hf5 "ix" nt_ix (by decide)).trans h4ix
  have h5out := (hf5 "out" nt_out (by decide)).trans h4out
  have h5ai := (hf5 "ai" nt_ai (by decide)).trans h4ai
  have h5nb := (hf5 "nb" nt_nb (by decide)).trans h4nb
  -- step 6: c1 := halfCarry ai nb
  obtain ⟨e6, hs6, h6c1, hf6⟩ := semScalar_setExpr_run (y := "c1")
    (lower_hc (envReadU64_of_bound h5ai) (envReadU64_of_bound h5nb) (by decide) (by decide))
  rw [halfCarry_evalBV, envReader_of_bound h5ai, envReader_of_bound h5nb] at h6c1
  have h6ix := (hf6 "ix" nt_ix (by decide)).trans h5ix
  have h6out := (hf6 "out" nt_out (by decide)).trans h5out
  have h6ai := (hf6 "ai" nt_ai (by decide)).trans h5ai
  have h6nb := (hf6 "nb" nt_nb (by decide)).trans h5nb
  have h6cx := (hf6 "cx" nt_cx (by decide)).trans h5cx
  -- step 7: s1 := (ai + nb) & mask64
  obtain ⟨e7, hs7, h7s1, hf7⟩ := semScalar_setExpr_run (y := "s1")
    (lower_addMask (envReadU64_of_bound h6ai) (envReadU64_of_bound h6nb))
  rw [mask_evalBV] at h7s1
  simp only [SExpr.evalBV, envReader_of_bound h6ai, envReader_of_bound h6nb] at h7s1
  have h7ix := (hf7 "ix" nt_ix (by decide)).trans h6ix
  have h7out := (hf7 "out" nt_out (by decide)).trans h6out
  have h7c1 := (hf7 "c1" nt_c1 (by decide)).trans h6c1
  have h7cx := (hf7 "cx" nt_cx (by decide)).trans h6cx
  -- step 8: c2 := halfCarry s1 cx
  obtain ⟨e8, hs8, h8c2, hf8⟩ := semScalar_setExpr_run (y := "c2")
    (lower_hc (envReadU64_of_bound h7s1) (envReadU64_of_bound h7cx) (by decide) (by decide))
  rw [halfCarry_evalBV, envReader_of_bound h7s1, envReader_of_bound h7cx] at h8c2
  have h8ix := (hf8 "ix" nt_ix (by decide)).trans h7ix
  have h8out := (hf8 "out" nt_out (by decide)).trans h7out
  have h8c1 := (hf8 "c1" nt_c1 (by decide)).trans h7c1
  have h8s1 := (hf8 "s1" nt_s1 (by decide)).trans h7s1
  have h8cx := (hf8 "cx" nt_cx (by decide)).trans h7cx
  -- step 9: df := (s1 + cx) & mask64
  obtain ⟨e9, hs9, h9df, hf9⟩ := semScalar_setExpr_run (y := "df")
    (lower_addMask (envReadU64_of_bound h8s1) (envReadU64_of_bound h8cx))
  rw [mask_evalBV] at h9df
  simp only [SExpr.evalBV, envReader_of_bound h8s1, envReader_of_bound h8cx] at h9df
  have h9ix := (hf9 "ix" nt_ix (by decide)).trans h8ix
  have h9out := (hf9 "out" nt_out (by decide)).trans h8out
  have h9c1 := (hf9 "c1" nt_c1 (by decide)).trans h8c1
  have h9c2 := (hf9 "c2" nt_c2 (by decide)).trans h8c2
  -- step 10: out[ix] := df
  obtain ⟨e10, hs10, h10out, hf10⟩ :=
    semScalar_arrStore (fw := 8 * N) h9out h9ix h9df
  rw [hivN] at h10out
  have h10c1 := (hf10 "c1" (by decide)).trans h9c1
  have h10c2 := (hf10 "c2" (by decide)).trans h9c2
  -- step 11: bw := (c1 + c2) ^ 1
  obtain ⟨e11, hs11, h11bw, hf11⟩ := semScalar_setExpr_run (y := "bw")
    (lower_addXorLit 1 (envReadU64_of_bound h10c1) (envReadU64_of_bound h10c2))
  simp only [SExpr.evalBV, envReader_of_bound h10c1, envReader_of_bound h10c2] at h11bw
  have h11out := (hf11 "out" nt_out (by decide)).trans h10out
  refine ⟨e11, ?_, ?_, ?_⟩
  · rw [hbody, seqAll_step hs1, seqAll_step hs2, seqAll_step hs3, seqAll_step hs4,
      seqAll_step hs5, seqAll_step hs6, seqAll_step hs7, seqAll_step hs8,
      seqAll_step hs9, seqAll_step hs10]
    exact hs11
  · rw [h11bw]; rfl
  · rw [h11out]; rfl

/-! ## 7. The runtime-trip programs' denotations and returned values -/

/-- The carry (borrow) seed slot `cy0seed`, which the export substitutes by `0`. -/
abbrev seedVar : Ctxt.Var ΓouterCarry r64 := .here

/-- The limb-count argument (RCX). -/
abbrev nVar : Ctxt.Var ΓouterCarry r64 := .there .here

/-- The second operand array (RDX). -/
abbrev bVar : Ctxt.Var ΓouterCarry AN := .there (.there .here)

/-- The first operand array (RSI). -/
abbrev aVar : Ctxt.Var ΓouterCarry AN := .there (.there (.there .here))

/-- The output array (RDI). -/
abbrev outVar : Ctxt.Var ΓouterCarry AN := .there (.there (.there (.there .here)))

/-- **The runtime-trip `mpn_add_n` program denotes the carry fold.** The compiled
    program's denotation at any valuation is `addCarryFold` of the argument slots:
    the trip count read from `n`, the operand arrays threaded as invariants, the
    seed slot as the carry-in. No front-compilation hypothesis remains. -/
theorem addRtProg_fold (V : Ctxt.Valuation ΓouterCarry) :
    addRtProgOpt.map (fun c => ComL.denote c V)
      = some (addCarryFold (aVar.lookup V) (bVar.lookup V) (nVar.lookup V).toNat
          (seedVar.lookup V)) := by
  refine (rolledForLoopNRt_denote (Γouter := ΓouterCarry) (accCTy := .sword 64)
    (invCTys := [.memref N, .memref N, .memref N]) vmBody "cy" addBodyLowCT
    (.there .here) .here _ addUpdate_eq V).trans (congrArg some ?_)
  have h64 := (nVar.lookup V).isLt
  exact frontLoopBodyJ_denote_foldl (accCTy := .sword 64)
    (invCTys := [.memref N, .memref N, .memref N]) vmBody "cy" addBodyLowCT addBody_covered
    (.cons (aVar.lookup V) (.cons (bVar.lookup V) (.cons (outVar.lookup V) .nil)))
    (fun c t => (addLimbW (memGetDyn (aVar.lookup V) t) (memGetDyn (bVar.lookup V) t) c).2)
    (nVar.lookup V).toNat
    (fun t c ht => by
      obtain ⟨env', hrun, hcy, -⟩ :=
        addLimbBody_run (aVar.lookup V) (bVar.lookup V) (outVar.lookup V) c t (by omega)
      exact ⟨carryEnv "cy" (aVar.lookup V) (bVar.lookup V) (outVar.lookup V) c
          (BitVec.ofNat 64 t), env',
        consistentS_addEnv (aVar.lookup V) (bVar.lookup V) (outVar.lookup V) c
          (BitVec.ofNat 64 t),
        hrun, hcy⟩)
    addUpdate_eq (seedVar.lookup V)

/-- **The runtime-trip `mpn_sub_n` program denotes the borrow fold.** As
    `addRtProg_fold`, for the borrow accumulator. -/
theorem subRtProg_fold (V : Ctxt.Valuation ΓouterCarry) :
    subRtProgOpt.map (fun c => ComL.denote c V)
      = some (subBorrowFold (aVar.lookup V) (bVar.lookup V) (nVar.lookup V).toNat
          (seedVar.lookup V)) := by
  refine (rolledForLoopNRt_denote (Γouter := ΓouterCarry) (accCTy := .sword 64)
    (invCTys := [.memref N, .memref N, .memref N]) vmBodySub "bw" subBodyLowCT
    (.there .here) .here _ subUpdate_eq V).trans (congrArg some ?_)
  have h64 := (nVar.lookup V).isLt
  exact frontLoopBodyJ_denote_foldl (accCTy := .sword 64)
    (invCTys := [.memref N, .memref N, .memref N]) vmBodySub "bw" subBodyLowCT subBody_covered
    (.cons (aVar.lookup V) (.cons (bVar.lookup V) (.cons (outVar.lookup V) .nil)))
    (fun c t => (subLimbW (memGetDyn (aVar.lookup V) t) (memGetDyn (bVar.lookup V) t) c).2)
    (nVar.lookup V).toNat
    (fun t c ht => by
      obtain ⟨env', hrun, hbw, -⟩ :=
        subLimbBody_run (aVar.lookup V) (bVar.lookup V) (outVar.lookup V) c t (by omega)
      exact ⟨carryEnv "bw" (aVar.lookup V) (bVar.lookup V) (outVar.lookup V) c
          (BitVec.ofNat 64 t), env',
        consistentS_subEnv (aVar.lookup V) (bVar.lookup V) (outVar.lookup V) c
          (BitVec.ofNat 64 t),
        hrun, hbw⟩)
    subUpdate_eq (seedVar.lookup V)

/-- The carry fold after `k ≤ NR` trips is the top carry of the operand sum:
    `(bignumVal a[0..k) + bignumVal b[0..k) + c₀) / 2^(64k)`, and lies in `{0, 1}`. -/
theorem addCarryFold_val {NA NB : Nat} (NR : Nat) (ap : Fin NA → BitVec 64)
    (bp : Fin NB → BitVec 64) (c₀ : BitVec 64) (hc₀ : c₀.toNat ≤ 1) (k : Nat) (hk : k ≤ NR) :
    (addCarryFold ap bp k c₀).toNat
        = (bignumVal (cells ap k) + bignumVal (cells bp k) + c₀.toNat) / (2 ^ 64) ^ k
      ∧ (addCarryFold ap bp k c₀).toNat ≤ 1 := by
  obtain ⟨hv, hc⟩ := addFold_val ap bp (fun _ : Fin NR => (0 : BitVec 64)) c₀ hc₀ k hk
  rw [addFold_snd] at hv hc
  refine ⟨?_, hc⟩
  have hlt := bignumVal_lt (cells (addFold ap bp k ((fun _ : Fin NR => (0 : BitVec 64)), c₀)).1 k)
  rw [cells_length] at hlt
  have hP : 0 < ((2 : Nat) ^ 64) ^ k := by positivity
  rw [← hv, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hlt, Nat.zero_add]

/-- The borrow fold after `k ≤ NR` trips is `1` exactly when the minuend prefix is
    below the subtrahend prefix plus the borrow-in, and `0` otherwise. -/
theorem subBorrowFold_val {NA NB : Nat} (NR : Nat) (ap : Fin NA → BitVec 64)
    (bp : Fin NB → BitVec 64) (bw₀ : BitVec 64) (hbw₀ : bw₀.toNat ≤ 1) (k : Nat)
    (hk : k ≤ NR) :
    (subBorrowFold ap bp k bw₀).toNat
      = if bignumVal (cells ap k) < bignumVal (cells bp k) + bw₀.toNat then 1 else 0 := by
  obtain ⟨hv, hc⟩ := subFold_val ap bp (fun _ : Fin NR => (0 : BitVec 64)) bw₀ hbw₀ k hk
  rw [subFold_snd] at hv hc
  have hlt := bignumVal_lt (cells (subFold ap bp k ((fun _ : Fin NR => (0 : BitVec 64)), bw₀)).1 k)
  rw [cells_length] at hlt
  generalize bignumVal (cells (subFold ap bp k ((fun _ : Fin NR => (0 : BitVec 64)), bw₀)).1 k)
    = D at hv hlt
  generalize ((2 : Nat) ^ 64) ^ k = P at hv hlt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h <;> rw [h] at hv ⊢ <;>
    split <;> omega

/-- **The compiled `mpn_add_n` returns the carry-out of the sum.** For a limb
    count within the arrays' width `N` and a seed in `{0, 1}` (the export
    substitutes `0`), the compiled program's denotation is a carry `c ∈ {0, 1}`
    with `c = (bignumVal a[0..n) + bignumVal b[0..n) + seed) / 2^(64n)`. -/
theorem addRtProg_val (V : Ctxt.Valuation ΓouterCarry)
    (hn : (nVar.lookup V).toNat ≤ N) (h0 : (seedVar.lookup V).toNat ≤ 1) :
    ∃ c : BitVec 64,
      addRtProgOpt.map (fun c => ComL.denote c V) = some c
        ∧ c.toNat = (bignumVal (cells (aVar.lookup V) (nVar.lookup V).toNat)
              + bignumVal (cells (bVar.lookup V) (nVar.lookup V).toNat)
              + (seedVar.lookup V).toNat) / (2 ^ 64) ^ (nVar.lookup V).toNat
        ∧ c.toNat ≤ 1 :=
  ⟨_, addRtProg_fold V,
    addCarryFold_val N (aVar.lookup V) (bVar.lookup V) (seedVar.lookup V) h0 _ hn⟩

/-- **The compiled `mpn_sub_n` returns the borrow-out of the difference.** For a
    limb count within the arrays' width `N` and a seed in `{0, 1}` (the export
    substitutes `0`), the compiled program's denotation is `1` exactly when
    `bignumVal a[0..n) < bignumVal b[0..n) + seed`, and `0` otherwise. -/
theorem subRtProg_val (V : Ctxt.Valuation ΓouterCarry)
    (hn : (nVar.lookup V).toNat ≤ N) (h0 : (seedVar.lookup V).toNat ≤ 1) :
    ∃ bw : BitVec 64,
      subRtProgOpt.map (fun c => ComL.denote c V) = some bw
        ∧ bw.toNat = if bignumVal (cells (aVar.lookup V) (nVar.lookup V).toNat)
              < bignumVal (cells (bVar.lookup V) (nVar.lookup V).toNat)
                + (seedVar.lookup V).toNat then 1 else 0 :=
  ⟨_, subRtProg_fold V,
    subBorrowFold_val N (aVar.lookup V) (bVar.lookup V) (seedVar.lookup V) h0 _ hn⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubFrontDenote
