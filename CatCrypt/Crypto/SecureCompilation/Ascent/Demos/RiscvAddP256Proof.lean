/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresRiscvMacros
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBignumKernel
public import CatCrypt.Crypto.SecureCompilation.FieldSpecs

/-!
# Correctness of the RV64 `bignum_add_p256` block

`RiscvBignumKernel.addp256Block64` is the `ROp64` body of s2n-bignum's
`bignum_add_p256` on RV64: the four-limb `sltu` carry chain, the `li` limbs of
`p256`, the `sltu` trial subtraction, and the mask select of the reduced limbs. Its
value is checked there on three vectors by `native_decide`. This module proves the
value for every input below `p256`: for every `RState64`, with `x` the limbs in
`d0..d3` and `y` the limbs in `n0..n3`, running the lowered block leaves
`(x + y) mod p256` in `d0..d3` and `n0..n3` unchanged.

The proof runs the eighteen ops through the transport lemmas of `CorresRiscvMacros`
(`run_addcc`, `run_addc`, `run_li`, `run_subbb`, `run_subb`, `run_xor`, `run_csub`),
collecting one `Nat` equation per carry op, and closes the value by `omega`
(`addp256_arith`). The result is then stated as a `CorresR` square over the state
relation `SRadd`, which reads the two four-limb values off the registers.

## Main results

* `addp256_arith`: the `Nat` content of the block, a lemma over limb words, carry and
  borrow bits.
* `addp256_run`: from a state described by `R`, the lowered block reaches a state whose
  `d` limbs hold `(x + y) mod p256` and whose `n` limbs are unchanged.
* `addp256_corresR`: the block refines `x := (x + y) mod p256` under `SRadd`, for inputs
  below `p256`.
* `sradd_satisfiable`: `SRadd` and the guard have a common witness.
* `addp256_correct`: the closed statement over `runRBlock64`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvAddP256Proof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBignumKernel
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.Ascent.RiscvMacros
open CatCrypt.Crypto.SecureCompilation.FieldSpecs (p256)

/-- `p256` as a numeral. -/
theorem p256_eq :
    p256 = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff := by
  unfold p256; norm_num

/-- The four little-endian limbs of `p256`, as `addp256Block64` materialises them. -/
theorem p256_limbs :
    0xffffffffffffffff + 2 ^ 64 * 0x00000000ffffffff + 2 ^ 192 * 0xffffffff00000001 = p256 := by
  rw [p256_eq]; norm_num

/-- The `Nat` content of `addp256Block64`. The `d` limbs after the carry chain are
    `d0..d3` with top carry `cy`; the trial subtraction of the limbs `P0, P1, 0, P3` of
    `p256` leaves `m0..m3` with borrow words `b1..b4` and final borrow `bo`; the select
    takes `m` when `bo = 0`. The carry and borrow words need no bound: the limb bounds
    and the equations determine them. -/
theorem addp256_arith (x0 x1 x2 x3 y0 y1 y2 y3 d0 d1 d2 d3 c1 c2 c3 cy m0 m1 m2 m3
    b1 b2 b3 b4 bo bf P0 P1 P3 z : Nat)
    (hd0 : d0 < 2 ^ 64) (hd1 : d1 < 2 ^ 64) (hd2 : d2 < 2 ^ 64) (hd3 : d3 < 2 ^ 64)
    (hm0 : m0 < 2 ^ 64) (hm1 : m1 < 2 ^ 64) (hm2 : m2 < 2 ^ 64) (hm3 : m3 < 2 ^ 64)
    (hbf : bf < 2 ^ 64) (hbo : bo ≤ 1)
    (hP0 : P0 = 0xffffffffffffffff) (hP1 : P1 = 0x00000000ffffffff)
    (hP3 : P3 = 0xffffffff00000001) (hz : z = 0)
    (e0 : d0 + 2 ^ 64 * c1 = x0 + y0) (e1 : d1 + 2 ^ 64 * c2 = x1 + y1 + c1)
    (e2 : d2 + 2 ^ 64 * c3 = x2 + y2 + c2) (e3 : d3 + 2 ^ 64 * cy = x3 + y3 + c3)
    (f0 : m0 + P0 = d0 + 2 ^ 64 * b1) (f1 : m1 + P1 + b1 = d1 + 2 ^ 64 * b2)
    (f2 : m2 + z + b2 = d2 + 2 ^ 64 * b3) (f3 : m3 + P3 + b3 = d3 + 2 ^ 64 * b4)
    (f4 : bf + z + b4 = cy + 2 ^ 64 * bo)
    (hx : x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 < p256)
    (hy : y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 < p256) :
    (if bo = 0 then m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3
      else d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3)
      = (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3
          + (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3)) % p256 := by
  subst hP0 hP1 hP3 hz
  -- the carry chain: the five-limb sum is `x + y`
  have hS : d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 + 2 ^ 256 * cy
      = (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3)
        + (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) := by omega
  -- the trial subtraction: `m + p256 = d + 2^256 · b4`
  have hM : m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3 + p256
      = d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 + 2 ^ 256 * b4 := by
    rw [← p256_limbs]; omega
  have hD : d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 < 2 ^ 256 := by omega
  have hMlt : m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3 < 2 ^ 256 := by omega
  generalize x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3 = X at *
  generalize y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 = Y at *
  generalize d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 = D at *
  generalize m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3 = M at *
  rw [p256_eq] at *
  split_ifs with h
  · have : M = X + Y - 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff := by
      omega
    rw [this, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- The abstract state of the block: the value in `d0..d3` and the value in `n0..n3`. -/
structure AAdd where
  /-- The value in `d0..d3`. -/
  x : Nat
  /-- The value in `n0..n3`. -/
  y : Nat

/-- `SRadd`: the machine's `d` and `n` limbs read as the abstract `x` and `y`. -/
def SRadd (s : RState64) (a : AAdd) : Prop :=
  limbs4 s.get "d0" "d1" "d2" "d3" = a.x ∧ limbs4 s.get "n0" "n1" "n2" "n3" = a.y

/-- From a state described by `R` with `x`, `y` below `p256`, the lowered block reaches
    a state whose `d` limbs hold `(x + y) mod p256` and whose `n` limbs are unchanged. -/
theorem addp256_run {R : AStateR} {s : RState64} (hs : SRr s R)
    (hx : limbs4 R "d0" "d1" "d2" "d3" < p256) (hy : limbs4 R "n0" "n1" "n2" "n3" < p256) :
    Reach (fun R' => limbs4 R' "d0" "d1" "d2" "d3"
        = (limbs4 R "d0" "d1" "d2" "d3" + limbs4 R "n0" "n1" "n2" "n3") % p256
      ∧ limbs4 R' "n0" "n1" "n2" "n3" = limbs4 R "n0" "n1" "n2" "n3")
      (runRBlock64 s (lowerRBlock64 addp256Block64)) := by
  have hz : (R "zero").toNat = 0 := by rw [SRr_zero hs]; rfl
  unfold addp256Block64
  simp only [lowerRBlock64_cons, lowerRBlock64_nil]
  refine run_addcc _ _ _ _ (by decide) hs ?_; intro D0 C1 s1 hs1 e0 hc1
  refine run_addc _ _ _ _ _ _ (by decide) hs1
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc1) ?_
  intro w1 w2 w3 w4 D1 C2 s2 hs2 e1 hc2
  refine run_addc _ _ _ _ _ _ (by decide) hs2
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc2) ?_
  intro w5 w6 w7 w8 D2 C3 s3 hs3 e2 hc3
  refine run_addc _ _ _ _ _ _ (by decide) hs3
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc3) ?_
  intro w9 w10 w11 w12 D3 CY s4 hs4 e3 hcy
  refine run_li _ _ (by decide) hs4 ?_; intro s5 hs5
  refine run_li _ _ (by decide) hs5 ?_; intro s6 hs6
  refine run_li _ _ (by decide) hs6 ?_; intro s7 hs7
  refine run_subbb _ _ _ _ (by decide) hs7 ?_; intro M0 B1 s8 hs8 f0 hb1
  refine run_subb _ _ _ _ _ _ (by decide) hs8
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hb1) ?_
  intro v1 v2 v3 v4 M1 B2 s9 hs9 f1 hb2
  refine run_subb _ _ _ _ _ _ (by decide) hs9
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hb2) ?_
  intro v5 v6 v7 v8 M2 B3 s10 hs10 f2 hb3
  refine run_subb _ _ _ _ _ _ (by decide) hs10
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hb3) ?_
  intro v9 v10 v11 v12 M3 B4 s11 hs11 f3 hb4
  refine run_subb _ _ _ _ _ _ (by decide) hs11
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hb4) ?_
  intro v13 v14 v15 v16 BF BO s12 hs12 f4 hbo
  refine run_li _ _ (by decide) hs12 ?_; intro s13 hs13
  refine run_xor _ _ _ (by decide) hs13 ?_; intro s14 hs14
  refine run_csub _ _ _ _ _ _ (by decide) hs14
    (by simp only [upd, ↓reduceIte, String.reduceEq, xor_one_toNat BO hbo]; omega) ?_
  intro u1 u2 u3 u4 Z0 s15 hs15 g0
  refine run_csub _ _ _ _ _ _ (by decide) hs15
    (by simp only [upd, ↓reduceIte, String.reduceEq, xor_one_toNat BO hbo]; omega) ?_
  intro u5 u6 u7 u8 Z1 s16 hs16 g1
  refine run_csub _ _ _ _ _ _ (by decide) hs16
    (by simp only [upd, ↓reduceIte, String.reduceEq, xor_one_toNat BO hbo]; omega) ?_
  intro u9 u10 u11 u12 Z2 s17 hs17 g2
  refine run_csub _ _ _ _ _ _ (by decide) hs17
    (by simp only [upd, ↓reduceIte, String.reduceEq, xor_one_toNat BO hbo]; omega) ?_
  intro u13 u14 u15 u16 Z3 s18 hs18 g3
  refine run_nil hs18 ⟨?_, ?_⟩
  · simp only [limbs4, upd, ↓reduceIte, String.reduceEq]
    simp only [upd, ↓reduceIte, String.reduceEq, xor_one_toNat BO hbo]
      at e1 e2 e3 f0 f1 f2 f3 f4 g0 g1 g2 g3
    unfold limbs4 at hx hy
    have key := addp256_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      D0.isLt D1.isLt D2.isLt D3.isLt M0.isLt M1.isLt M2.isLt M3.isLt BF.isLt
      hbo rfl rfl rfl hz e0 e1 e2 e3 f0 f1 f2 f3 f4 hx hy
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbo with h0 | h1
    · simp only [h0, Nat.sub_zero, ↓reduceIte] at g0 g1 g2 g3 key
      subst g0 g1 g2 g3
      exact key
    · simp only [h1, Nat.sub_self, ↓reduceIte, Nat.zero_ne_one, Nat.one_ne_zero] at g0 g1 g2 g3 key
      subst g0 g1 g2 g3
      exact key
  · simp only [limbs4, upd, ↓reduceIte, String.reduceEq]

/-- **`addp256Block64` refines `x := (x + y) mod p256`.** Under `SRadd`, from inputs
    below `p256`, running the lowered block lands in the state with `x` replaced by the
    reduced sum and `y` unchanged. -/
theorem addp256_corresR :
    CorresR SRadd (fun a => a.x < p256 ∧ a.y < p256)
      (fun a => ⟨(a.x + a.y) % p256, a.y⟩) (lowerRBlock64 addp256Block64) := by
  intro s a ⟨hx, hy⟩ ⟨hxp, hyp⟩
  obtain ⟨R', hs', h1, h2⟩ := addp256_run (SRr_self s) (hx ▸ hxp) (hy ▸ hyp)
  have hR' : (runRBlock64 s (lowerRBlock64 addp256Block64)).get = R' := funext hs'
  exact ⟨by rw [hR', h1, hx, hy], by rw [hR', h2, hy]⟩

/-- `SRadd` and the guard of `addp256_corresR` have a common witness. -/
theorem sradd_satisfiable : ∃ s a, SRadd s a ∧ a.x < p256 ∧ a.y < p256 :=
  ⟨{ regs := fun _ => 0 }, ⟨0, 0⟩, by simp [SRadd, limbs4, RState64.get],
    by unfold p256; decide, by unfold p256; decide⟩

/-- **The RV64 `bignum_add_p256` body is correct.** For every machine state whose limbs
    `d0..d3` and `n0..n3` hold `x` and `y` below `p256`, running the lowered block leaves
    `(x + y) mod p256` in `d0..d3`. -/
theorem addp256_correct (s : RState64)
    (hx : limbs4 s.get "d0" "d1" "d2" "d3" < p256)
    (hy : limbs4 s.get "n0" "n1" "n2" "n3" < p256) :
    limbs4 (runRBlock64 s (lowerRBlock64 addp256Block64)).get "d0" "d1" "d2" "d3"
      = (limbs4 s.get "d0" "d1" "d2" "d3" + limbs4 s.get "n0" "n1" "n2" "n3") % p256 :=
  (addp256_corresR s ⟨_, _⟩ ⟨rfl, rfl⟩ ⟨hx, hy⟩).1

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvAddP256Proof.addp256_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms addp256_correct

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvAddP256Proof
