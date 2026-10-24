/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.WhileFun
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar
public import CatCrypt.Crypto.Jasmin.LowCTNotation
public import Mathlib.Tactic.Ring

/-!
# Demo: the functional `while` rule on a summation loop

The kernel is the `LowCT` do-while

```
do { acc := acc + k; k := k - 1 } while (k != 0)
```

over 64-bit words, related to the abstract state `String → BitVec 64` by `SRwordBV`.
Its abstract step is `sumStep`, its abstract guard `sumGuard`, and the exit state of
the abstract loop is stated explicitly as `sumExit`: `k` is `0` and `acc` has grown
by `k (k + 1) / 2`, where `k` is read as a natural number.

`sum_loopRecIn` proves, by induction on the value of the loop variable `k`, that the
abstract loop from any state exits in `sumExit` after `k` trips. The same induction
gives termination (`sum_terminates`) and the value of `loopFun` (`sum_loopFun`), so
the abstract function carries no fuel.

## Main results

* `sumBody_corresU` — the body correspondence, from two `corres_setExprWord` leaves
* `sumLoop_corres` — every terminating run of the kernel lands in a state related to
  `sumExit (sumStep a)`
* `sumLoop_total` — with fuel above `(a "k" - 1).toNat`, the kernel run terminates
* `sumLoop_corres_of_ne_zero` — for `a "k" ≠ 0` the related state is `sumExit a`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Ascent

/-- The loop body: `acc := acc + k; k := k - 1`. -/
def sumBody : LowCT := lowct% acc := acc + k; k := k - 1

/-- The kernel: the body, repeated while `k` is nonzero. -/
def sumLoop : LowCT := lowct% while k { ↑sumBody }

/-- The abstract step of the body. -/
def sumStep (a : String → BitVec 64) : String → BitVec 64 :=
  fun s => if s = "k" then a "k" - 1 else if s = "acc" then a "acc" + a "k" else a s

/-- The abstract guard: `k` is nonzero. -/
def sumGuard (a : String → BitVec 64) : Bool := decide (a "k" ≠ 0)

/-- The exit state of the abstract loop from `a`: `k` is `0`, `acc` is increased by
    the `k`-th triangular number, and every other name is unchanged. -/
def sumExit (a : String → BitVec 64) : String → BitVec 64 :=
  fun s => if s = "k" then 0
    else if s = "acc" then a "acc" + BitVec.ofNat 64 ((a "k").toNat * ((a "k").toNat + 1) / 2)
    else a s

theorem sumBody_corresU (fuel : Nat) :
    CorresU fuel SRwordBV (fun _ => True) sumStep sumBody := by
  have h := corresU_seq (fuel := fuel) SRwordBV
    (corresU_of_corres (fuel := fuel) SRwordBV rfl
      (corres_setExprWord "acc" (.SAdd (.SVar "acc") (.SVar "k"))
        ⟨notTmp_of_short "acc" (by decide), notTmp_of_short "k" (by decide)⟩))
    (corresU_of_corres (fuel := fuel) SRwordBV rfl
      (corres_setExprWord "k" (.SSub (.SVar "k") (.SLit 1))
        ⟨notTmp_of_short "k" (by decide), (by norm_num : (1 : ℕ) < 2 ^ 64)⟩))
    (fun _ _ => trivial)
  intro env a hSR hP
  obtain ⟨env', hrun, hSR'⟩ := h env a hSR hP
  refine ⟨env', hrun, ?_⟩
  have heq : (fun s => if s = "k" then
        SExpr.evalBV (fun s => if s = "acc" then SExpr.evalBV a (.SAdd (.SVar "acc") (.SVar "k"))
          else a s) (.SSub (.SVar "k") (.SLit 1))
      else (fun s => if s = "acc" then SExpr.evalBV a (.SAdd (.SVar "acc") (.SVar "k"))
          else a s) s) = sumStep a := by
    funext s
    by_cases hk : s = "k"
    · subst hk; simp [sumStep, SExpr.evalBV]
    · by_cases hacc : s = "acc"
      · subst hacc; simp [sumStep, SExpr.evalBV]
      · simp [sumStep, hk, hacc]
  rw [← heq]
  exact hSR'

theorem sum_guard (env : SEnvScalar) (a : String → BitVec 64) (hSR : SRwordBV env a)
    (_ : True) : guardNz "k" env = sumGuard a := by
  have hk := hSR "k" (notTmp_of_short "k" (by decide))
  simp [guardNz, envReadU64, hk, sumGuard]

/-- One trip from a state with `k ≠ 0` leaves the exit state unchanged. -/
theorem sumExit_sumStep (a : String → BitVec 64) (hk : a "k" ≠ 0) :
    sumExit (sumStep a) = sumExit a := by
  obtain ⟨n, hn⟩ : ∃ n, (a "k").toNat = n + 1 := by
    refine ⟨(a "k").toNat - 1, ?_⟩
    have : (a "k").toNat ≠ 0 := fun h => hk (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  have hstepk : (sumStep a "k").toNat = n := by
    simp only [sumStep, ite_true]
    bv_omega
  have htri : (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
    have : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
    rw [this, Nat.add_mul_div_left _ _ (by decide)]
  funext s
  by_cases hsk : s = "k"
  · simp [sumExit, hsk]
  · by_cases hsa : s = "acc"
    · subst hsa
      simp only [sumExit, hstepk, hn, htri, BitVec.ofNat_add]
      simp only [sumStep, hsk, ite_false, ite_true]
      have hak : a "k" = BitVec.ofNat 64 (n + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hn, BitVec.toNat_ofNat]
        have := (a "k").isLt
        omega
      rw [hak]
      simp only [BitVec.ofNat_add]
      ac_rfl
    · simp [sumExit, sumStep, hsk, hsa]

/-- The abstract loop from `a` exits in `sumExit a` after `(a "k").toNat` trips,
    by induction on the value of `k`. -/
theorem sum_loopRecIn :
    ∀ (n : Nat) (a : String → BitVec 64), (a "k").toNat = n →
      LoopRecIn sumGuard sumStep n a (sumExit a) := by
  intro n
  induction n with
  | zero =>
      intro a hn
      have hk : a "k" = 0 := BitVec.eq_of_toNat_eq (by simpa using hn)
      have hexit : sumExit a = a := by
        funext s
        by_cases hsk : s = "k"
        · subst hsk; simp [sumExit, hk]
        · by_cases hsa : s = "acc"
          · subst hsa; simp [sumExit, hn]
          · simp [sumExit, hsk, hsa]
      rw [hexit]
      exact .exit (by simp [sumGuard, hk])
  | succ n ih =>
      intro a hn
      have hk : a "k" ≠ 0 := by
        intro h; rw [h] at hn; simp at hn
      have hstepk : (sumStep a "k").toNat = n := by
        simp only [sumStep, ite_true]
        bv_omega
      rw [← sumExit_sumStep a hk]
      exact .iter (by simpa only [sumGuard, decide_eq_true_eq] using hk) (ih (sumStep a) hstepk)

theorem sum_terminates (a : String → BitVec 64) : LoopTerminates sumGuard sumStep a :=
  ⟨_, _, sum_loopRecIn _ a rfl⟩

theorem sum_loopFun (a : String → BitVec 64) (h : LoopTerminates sumGuard sumStep a) :
    loopFun sumGuard sumStep a h = sumExit a :=
  loopFun_eq_of_loopRecIn (sum_loopRecIn _ a rfl) h

/-- Every terminating run of the kernel lands in a state related to
    `sumExit (sumStep a)`. -/
theorem sumLoop_corres (fuel : Nat) (env : SEnvScalar) (a : String → BitVec 64)
    (env' : SEnvScalar) (hSR : SRwordBV env a) (hrun : semU fuel sumLoop env = some env') :
    SRwordBV env' (sumExit (sumStep a)) := by
  have := corresU_whileFun SRwordBV (sumBody_corresU fuel) (fun _ _ => trivial) sum_guard
    env a env' hSR trivial hrun (sum_terminates _)
  rwa [sum_loopFun] at this

/-- With fuel above `(a "k" - 1).toNat`, the kernel run terminates in a state related
    to `sumExit (sumStep a)`. -/
theorem sumLoop_total (fuel : Nat) (env : SEnvScalar) (a : String → BitVec 64)
    (hSR : SRwordBV env a) (hfuel : (a "k" - 1).toNat < fuel) :
    ∃ env', semU fuel sumLoop env = some env' ∧ SRwordBV env' (sumExit (sumStep a)) := by
  have htrips : loopTrips sumGuard sumStep (sumStep a) (sum_terminates _) = (a "k" - 1).toNat :=
    loopTrips_eq_of_loopRecIn (sum_loopRecIn _ _ (by simp [sumStep])) _
  have := corresU_whileFun_total SRwordBV (sumBody_corresU fuel) (fun _ _ => trivial) sum_guard
    env a hSR trivial (sum_terminates _) (by rw [htrips]; exact hfuel)
  rwa [sum_loopFun] at this

/-- From an entry state with `k ≠ 0`, every terminating run of the kernel lands in a
    state where `k` is `0` and `acc` is increased by `k (k + 1) / 2`. -/
theorem sumLoop_corres_of_ne_zero (fuel : Nat) (env : SEnvScalar) (a : String → BitVec 64)
    (env' : SEnvScalar) (hSR : SRwordBV env a) (hk : a "k" ≠ 0)
    (hrun : semU fuel sumLoop env = some env') :
    SRwordBV env' (sumExit a) := by
  rw [← sumExit_sumStep a hk]
  exact sumLoop_corres fuel env a env' hSR hrun

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
