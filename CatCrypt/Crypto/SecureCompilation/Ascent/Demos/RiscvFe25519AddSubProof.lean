/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresRiscvMacros
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel
public import Mathlib.Data.ZMod.Basic

/-!
# Correctness of the RV64 Curve25519 add, subtract, `a24` multiply and swap blocks

`RiscvX25519FieldKernel` lowers the X25519 field operations to `ROp64` blocks over four
little-endian limbs: `x` in `q0..q3`, `y` in `y0..y3`, the result in `z0..z3`. Their
values are checked there by `native_decide` on worked vectors. This module proves them
for all inputs, over `runRBlock64`:

* `feAddBlock` leaves `(x + y) mod p25519` in `z0..z3`, for every `x, y < 2^256`;
* `feSubBlock` leaves `(x + 2·p25519 − y) mod p25519`, when `y ≤ x + 2·p25519` (in
  particular for every `y ≤ 2·p25519 = 2^256 − 38`);
* `feMul121666Block` leaves `121666 · x mod p25519`, for every `x < 2^256`;
* `cswapBlock` exchanges `a0..a3` and `b0..b3` when the word in `swap` is `1` and leaves
  them when it is `0`.

The field results are canonical (below `p25519`) and are restated in `ZMod p25519`.

## Structure

The three field blocks end in the same reduction `fold5 a0 a1 a2 a3 a4 z0 z1 z2 z3`:
two carry folds of the five-limb value `A = a₀..a₃ + 2^256·a₄` through `2^256 ≡ 38`,
then `condSubP`, which is one fourteen-op conditional subtraction of `p25519` (`passZ`)
run twice. The proofs follow that structure:

* `pass_run`: one pass leaves `csubP v` (`v − p25519` if `v ≥ p25519`, else `v`);
* `fold5_run`: for any input registers outside `fold5Writes` and `a₄ < 2^20`, the
  reduction leaves `A mod p25519` (`fold_mod`: the folded value `V` satisfies
  `A = V + 2·p25519·(a₄ + cy)`, and `V < 2^256 < 3·p25519`, so two passes reach
  `V mod p25519`, `csubP_csubP`);
* `feAdd_run`, `feSub_run`, `feMul121666_run`: each block's prefix through the transport
  lemmas of `CorresRiscvMacros`, then `fold5_run`.

Each run lemma also records that the input limbs `q0..q3`, `y0..y3` are unchanged, which
gives the `CorresR` squares over `SRfe`.

## Main results

* `pass_run`, `fold5_run`: the conditional subtraction and the reduction.
* `feAdd_correct`, `feSub_correct`, `feMul121666_correct`: the value in `z0..z3`.
* `feAdd_correct_zmod`, `feSub_correct_zmod`, `feMul121666_correct_zmod`: the same in
  `ZMod p25519`, with the result below `p25519`.
* `feAdd_corresR`, `feSub_corresR`, `feMul121666_corresR`: the blocks as `CorresR`
  squares over `SRfe`, with witness `srfe_satisfiable`.
* `cswap_correct`: the conditional swap.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519AddSubProof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.Ascent.RiscvMacros

/-! ## Arithmetic -/

theorem p25519_eq :
    p25519 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed := by
  unfold p25519; rfl

/-- The four limbs of `p25519` that `condSubP` materialises. -/
theorem p25519_limbs : 0xffffffffffffffed + 2 ^ 64 * 0xffffffffffffffff
    + 2 ^ 128 * 0xffffffffffffffff + 2 ^ 192 * 0x7fffffffffffffff = p25519 := by
  rw [p25519_eq]; rfl

/-- The four limbs of `2·p25519 = 2^256 − 38` that `feSubBlock` materialises. -/
theorem two_p25519_limbs : 0xffffffffffffffda + 2 ^ 64 * 0xffffffffffffffff
    + 2 ^ 128 * 0xffffffffffffffff + 2 ^ 192 * 0xffffffffffffffff = 2 * p25519 := by
  rw [p25519_eq]; rfl

/-- One conditional subtraction of `p25519`. -/
def csubP (v : Nat) : Nat := if p25519 ≤ v then v - p25519 else v

/-- The select of one pass: the subtracted value when the trial subtraction does not
    borrow, the input otherwise. -/
theorem pass_select (M V bo : Nat) (hM : M < 2 ^ 256) (hV : V < 2 ^ 256) (hbo : bo ≤ 1)
    (h : M + p25519 = V + 2 ^ 256 * bo) : (if bo = 0 then M else V) = csubP V := by
  unfold csubP; rw [p25519_eq] at *; split <;> split <;> omega

/-- Two passes reduce any four-limb value, since `2^256 < 3·p25519`. -/
theorem csubP_csubP (v : Nat) (hv : v < 2 ^ 256) : csubP (csubP v) = v % p25519 := by
  unfold csubP; rw [p25519_eq] at *
  by_cases h1 : 57896044618658097711785492504343953926634992332820282019728792003956564819949 ≤ v
  · rw [if_pos h1]
    by_cases h2 : 57896044618658097711785492504343953926634992332820282019728792003956564819949
        ≤ v - 57896044618658097711785492504343953926634992332820282019728792003956564819949
    · rw [if_pos h2, Nat.mod_eq_sub_mod h1, Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)]
    · rw [if_neg h2, Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h1, if_neg h1, Nat.mod_eq_of_lt (by omega)]

/-- The two carry folds of `fold5`: the first leaves `V₁` with carry `cy`, the second
    `V₂`; the second fold does not wrap, and `V₂ ≡ lo + 2^256·a₄` modulo `p25519`. -/
theorem fold_mod (lo V1 V2 a4 cy cz : Nat) (hlo : lo < 2 ^ 256) (hV1 : V1 < 2 ^ 256)
    (hV2 : V2 < 2 ^ 256) (ha4 : a4 < 2 ^ 20)
    (h1 : V1 + 2 ^ 256 * cy = lo + 38 * a4) (h2 : V2 + 2 ^ 256 * cz = V1 + 38 * cy) :
    V2 % p25519 = (lo + 2 ^ 256 * a4) % p25519 := by
  have hcz : cz = 0 := by omega
  subst hcz
  have : lo + 2 ^ 256 * a4 = V2 + p25519 * (2 * (a4 + cy)) := by
    rw [p25519_eq]; omega
  rw [this, Nat.add_mul_mod_self_left]

/-- The trial subtraction of one pass, as one equation over the four-limb values. -/
theorem pass_sum (v0 v1 v2 v3 m0 m1 m2 m3 b1 b2 b3 bo P0 P1 P2 P3 : Nat)
    (hP0 : P0 = 0xffffffffffffffed) (hP1 : P1 = 0xffffffffffffffff)
    (hP2 : P2 = 0xffffffffffffffff) (hP3 : P3 = 0x7fffffffffffffff)
    (f0 : m0 + P0 = v0 + 2 ^ 64 * b1) (f1 : m1 + P1 + b1 = v1 + 2 ^ 64 * b2)
    (f2 : m2 + P2 + b2 = v2 + 2 ^ 64 * b3) (f3 : m3 + P3 + b3 = v3 + 2 ^ 64 * bo) :
    m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3 + p25519
      = v0 + 2 ^ 64 * v1 + 2 ^ 128 * v2 + 2 ^ 192 * v3 + 2 ^ 256 * bo := by
  subst hP0 hP1 hP2 hP3; rw [← p25519_limbs]; omega

/-- A product by a small constant does not wrap. -/
theorem mul_small_toNat (x : X64R) (k : Nat) (hk : k < 2 ^ 44) (hx : x.toNat < 2 ^ 20) :
    (x * BitVec.ofNat 64 k).toNat = x.toNat * k := by
  have hlt : x.toNat * k < 2 ^ 64 :=
    calc x.toNat * k < 2 ^ 20 * 2 ^ 44 := Nat.mul_lt_mul'' hx hk
      _ = 2 ^ 64 := by rfl
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt hlt]

/-- A four-limb add-with-carry chain as one equation. -/
theorem chain_add4 (a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 c1 c2 c3 c4 : Nat)
    (e0 : d0 + 2 ^ 64 * c1 = a0 + b0) (e1 : d1 + 2 ^ 64 * c2 = a1 + b1 + c1)
    (e2 : d2 + 2 ^ 64 * c3 = a2 + b2 + c2) (e3 : d3 + 2 ^ 64 * c4 = a3 + b3 + c3) :
    d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 + 2 ^ 256 * c4
      = (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3)
        + (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) := by
  omega

/-- A five-limb subtract-with-borrow chain, the top limb subtracting `0`, as one
    equation. -/
theorem chain_sub5 (s0 s1 s2 s3 s4 y0 y1 y2 y3 a0 a1 a2 a3 a4 g1 g2 g3 g4 gf z : Nat)
    (hz : z = 0)
    (f0 : a0 + y0 = s0 + 2 ^ 64 * g1) (f1 : a1 + y1 + g1 = s1 + 2 ^ 64 * g2)
    (f2 : a2 + y2 + g2 = s2 + 2 ^ 64 * g3) (f3 : a3 + y3 + g3 = s3 + 2 ^ 64 * g4)
    (f4 : a4 + z + g4 = s4 + 2 ^ 64 * gf) :
    (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4)
        + (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3)
      = (s0 + 2 ^ 64 * s1 + 2 ^ 128 * s2 + 2 ^ 192 * s3 + 2 ^ 256 * s4) + 2 ^ 320 * gf := by
  subst hz; omega

/-- A subtraction that cannot borrow: from `A + Y = S + 2^320·g` with `A < 2^320` and
    `Y ≤ S`, the borrow is `0` and `A = S − Y`. -/
theorem sub_no_borrow (A Y S g : Nat) (hA : A < 2 ^ 320) (hY : Y ≤ S)
    (h : A + Y = S + 2 ^ 320 * g) : g = 0 ∧ A = S - Y := by
  omega

/-- Five limbs are below `2^320`. -/
theorem limbs5_lt (a0 a1 a2 a3 a4 : X64R) :
    a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat
      + 2 ^ 256 * a4.toNat < 2 ^ 320 := by
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt; have := a4.isLt
  omega

/-- The top limb of a five-limb value at most `x + 2·p25519`, with `x < 2^256`, is at
    most `1`. -/
theorem top_le_one (lo a4 x : Nat) (hx : x < 2 ^ 256)
    (h : lo + 2 ^ 256 * a4 ≤ x + 2 * p25519) : a4 ≤ 1 := by
  rw [p25519_eq] at h; omega

/-- The partial products of `121666 · x` accumulated by `feMul121666Block`. `lₖ, hₖ` are
    the low and high words of `xₖ · 121666`; the chain leaves `a₀..a₄` with `a₀ = l₀`. -/
theorem mul121666_arith (x0 x1 x2 x3 l0 l1 l2 l3 h0 h1 h2 h3 a1 a2 a3 a4 p1 p2 p3 p4 : Nat)
    (hx3 : x3 < 2 ^ 64) (ha4 : a4 < 2 ^ 64)
    (r0 : l0 + 2 ^ 64 * h0 = x0 * 121666) (r1 : l1 + 2 ^ 64 * h1 = x1 * 121666)
    (r2 : l2 + 2 ^ 64 * h2 = x2 * 121666) (r3 : l3 + 2 ^ 64 * h3 = x3 * 121666)
    (e1 : a1 + 2 ^ 64 * p1 = h0 + l1) (e2 : a2 + 2 ^ 64 * p2 = h1 + l2 + p1)
    (e3 : a3 + 2 ^ 64 * p3 = h2 + l3 + p2) (e4 : a4 + 2 ^ 64 * p4 = h3 + p3)
    (hp3 : p3 ≤ 1) :
    a4 < 2 ^ 20 ∧ l0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4
      = 121666 * (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) := by
  have hh3 : h3 < 121666 := by omega
  have hp4 : p4 = 0 := by omega
  subst hp4
  omega

/-! ## The conditional subtraction -/

/-- One pass of `condSubP` at the output registers `z0..z3`. -/
def passZ : List ROp64 :=
  [ .li "pp0" 0xffffffffffffffed, .li "pp1" 0xffffffffffffffff
  , .li "pp2" 0xffffffffffffffff, .li "pp3" 0x7fffffffffffffff
  , .subbb "m0" "bo1" "z0" "pp0"
  , .subb "m1" "bo2" "z1" "pp1" "bo1" "tt__"
  , .subb "m2" "bo3" "z2" "pp2" "bo2" "tt__"
  , .subb "m3" "bo" "z3" "pp3" "bo3" "tt__"
  , .li "one" 1, .xor "cond" "bo" "one"
  , .csub "z0" "m0" "z0" "cond" "mask" "tt__"
  , .csub "z1" "m1" "z1" "cond" "mask" "tt__"
  , .csub "z2" "m2" "z2" "cond" "mask" "tt__"
  , .csub "z3" "m3" "z3" "cond" "mask" "tt__" ]

theorem condSubP_z : condSubP "z0" "z1" "z2" "z3" = passZ ++ passZ := rfl

/-- The registers `fold5 _ _ _ _ _ z0 z1 z2 z3` writes, its expansion scratch included. -/
def fold5Writes : List String :=
  [ "c38", "fl", "z0", "z1", "z2", "z3", "cy1", "cy2", "cy3", "cy", "cz1", "cz2", "cz3",
    "cz4", "sum__", "tt__", "c1__", "c2__", "pp0", "pp1", "pp2", "pp3", "m0", "m1", "m2",
    "m3", "bo1", "bo2", "bo3", "bo", "b1__", "b2__", "dif__", "one", "cond", "mask",
    "csm__" ]

/-- One pass leaves `csubP` of the value in `z0..z3`, and writes only `fold5Writes`. -/
theorem pass_run {R : AStateR} {s : RState64} (hs : SRr s R) :
    Reach (fun R' => limbs4 R' "z0" "z1" "z2" "z3" = csubP (limbs4 R "z0" "z1" "z2" "z3")
      ∧ ∀ r, r ∉ fold5Writes → R' r = R r)
      (runRBlock64 s (lowerRBlock64 passZ)) := by
  unfold passZ
  simp only [lowerRBlock64_cons, lowerRBlock64_nil]
  refine run_li _ _ (by decide) hs ?_; intro s1 hs1
  refine run_li _ _ (by decide) hs1 ?_; intro s2 hs2
  refine run_li _ _ (by decide) hs2 ?_; intro s3 hs3
  refine run_li _ _ (by decide) hs3 ?_; intro s4 hs4
  refine run_subbb _ _ _ _ (by decide) hs4 ?_; intro M0 B1 s5 hs5 f0 hb1
  refine run_subb _ _ _ _ _ _ (by decide) hs5
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hb1) ?_
  intro _ _ _ _ M1 B2 s6 hs6 f1 hb2
  refine run_subb _ _ _ _ _ _ (by decide) hs6
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hb2) ?_
  intro _ _ _ _ M2 B3 s7 hs7 f2 hb3
  refine run_subb _ _ _ _ _ _ (by decide) hs7
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hb3) ?_
  intro _ _ _ _ M3 BO s8 hs8 f3 hbo
  refine run_li _ _ (by decide) hs8 ?_; intro s9 hs9
  refine run_xor _ _ _ (by decide) hs9 ?_; intro s10 hs10
  refine run_csub _ _ _ _ _ _ (by decide) hs10
    (by simp only [upd, ↓reduceIte, String.reduceEq, xor_one_toNat BO hbo]; omega) ?_
  intro _ _ _ _ Z0 s11 hs11 g0
  refine run_csub _ _ _ _ _ _ (by decide) hs11
    (by simp only [upd, ↓reduceIte, String.reduceEq, xor_one_toNat BO hbo]; omega) ?_
  intro _ _ _ _ Z1 s12 hs12 g1
  refine run_csub _ _ _ _ _ _ (by decide) hs12
    (by simp only [upd, ↓reduceIte, String.reduceEq, xor_one_toNat BO hbo]; omega) ?_
  intro _ _ _ _ Z2 s13 hs13 g2
  refine run_csub _ _ _ _ _ _ (by decide) hs13
    (by simp only [upd, ↓reduceIte, String.reduceEq, xor_one_toNat BO hbo]; omega) ?_
  intro _ _ _ _ Z3 s14 hs14 g3
  refine run_nil hs14 ⟨?_, ?_⟩
  · simp only [upd, ↓reduceIte, String.reduceEq, xor_one_toNat BO hbo]
      at f0 f1 f2 f3 g0 g1 g2 g3
    have hsum := pass_sum _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl f0 f1 f2 f3
    have key := pass_select _ _ _
      (by have := M0.isLt; have := M1.isLt; have := M2.isLt; have := M3.isLt; omega)
      (limbs4_lt R "z0" "z1" "z2" "z3") hbo hsum
    simp only [limbs4, upd, ↓reduceIte, String.reduceEq]
    unfold limbs4 at key
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbo with h0 | h1
    · simp only [h0, Nat.sub_zero, ↓reduceIte] at g0 g1 g2 g3 key
      subst g0 g1 g2 g3
      exact key
    · simp only [h1, Nat.sub_self, ↓reduceIte, Nat.zero_ne_one, Nat.one_ne_zero]
        at g0 g1 g2 g3 key
      subst g0 g1 g2 g3
      exact key
  · intro r hr
    simp only [fold5Writes, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [upd, hr, ↓reduceIte]

/-- The two passes of `condSubP` leave the value in `z0..z3` reduced modulo `p25519`. -/
theorem pass2_run {R : AStateR} {s : RState64} (hs : SRr s R) :
    Reach (fun R' => limbs4 R' "z0" "z1" "z2" "z3" = limbs4 R "z0" "z1" "z2" "z3" % p25519
      ∧ ∀ r, r ∉ fold5Writes → R' r = R r)
      (runRBlock64 s (lowerRBlock64 (passZ ++ passZ))) := by
  rw [lowerRBlock64_append, RISCVBackend.runRBlock64_append]
  obtain ⟨R1, hs1, hv1, hf1⟩ := pass_run hs
  obtain ⟨R2, hs2, hv2, hf2⟩ := pass_run hs1
  refine ⟨R2, hs2, ?_, fun r hr => by rw [hf2 r hr, hf1 r hr]⟩
  rw [hv2, hv1, csubP_csubP _ (limbs4_lt R _ _ _ _)]

/-- The scratch condition of the `addc` links of `fold5`, from the input register being
    outside `tt__`. -/
theorem addcOK_fold {d cout a cin : String} (hlit : AddcOK d cout "c38" "zero" cin "tt__")
    (ha : a ≠ "tt__") : AddcOK d cout a "zero" cin "tt__" := by
  obtain ⟨h1, h2, h3, h4, _, h6, h7, h8, h9, h10⟩ := hlit
  exact ⟨h1, h2, h3, h4, Ne.symm ha, h6, h7, h8, h9, h10⟩

/-! ## The reduction `fold5` -/

/-- The input registers of `fold5` are outside the registers it writes. -/
def Fold5OK (a0 a1 a2 a3 a4 : String) : Prop :=
  a0 ∉ fold5Writes ∧ a1 ∉ fold5Writes ∧ a2 ∉ fold5Writes ∧ a3 ∉ fold5Writes ∧
    a4 ∉ fold5Writes

instance (a0 a1 a2 a3 a4 : String) : Decidable (Fold5OK a0 a1 a2 a3 a4) := by
  unfold Fold5OK; infer_instance

/-- **The reduction.** For input registers outside `fold5Writes` holding the five-limb
    value `A = a₀..a₃ + 2^256·a₄` with `a₄ < 2^20`, `fold5 … z0 z1 z2 z3` leaves
    `A mod p25519` in `z0..z3` and writes only `fold5Writes`. -/
theorem fold5_run {a0 a1 a2 a3 a4 : String} (ha : Fold5OK a0 a1 a2 a3 a4)
    {R : AStateR} {s : RState64} (hs : SRr s R) (h4 : (R a4).toNat < 2 ^ 20) :
    Reach (fun R' => limbs4 R' "z0" "z1" "z2" "z3"
        = (limbs4 R a0 a1 a2 a3 + 2 ^ 256 * (R a4).toNat) % p25519
      ∧ ∀ r, r ∉ fold5Writes → R' r = R r)
      (runRBlock64 s (lowerRBlock64 (fold5 a0 a1 a2 a3 a4 "z0" "z1" "z2" "z3"))) := by
  have hz : (R "zero").toNat = 0 := by rw [SRr_zero hs]; rfl
  simp only [Fold5OK, fold5Writes, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
  unfold fold5
  rw [condSubP_z]
  simp only [List.cons_append, List.nil_append, lowerRBlock64_cons]
  refine run_li _ _ (by decide) hs ?_; intro s1 hs1
  refine run_mul _ _ _ (by decide) hs1 ?_; intro s2 hs2
  refine run_addcc _ _ _ _ (by simp [AddccOK, NZ, ha]) hs2 ?_; intro D0 C1 s3 hs3 e0 hc1
  refine run_addc _ _ _ _ _ _ (addcOK_fold (by decide) (by intro h; simp [h] at ha)) hs3
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc1) ?_
  intro _ _ _ _ D1 C2 s4 hs4 e1 hc2
  refine run_addc _ _ _ _ _ _ (addcOK_fold (by decide) (by intro h; simp [h] at ha)) hs4
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc2) ?_
  intro _ _ _ _ D2 C3 s5 hs5 e2 hc3
  refine run_addc _ _ _ _ _ _ (addcOK_fold (by decide) (by intro h; simp [h] at ha)) hs5
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc3) ?_
  intro _ _ _ _ D3 CY s6 hs6 e3 hcy
  refine run_mul _ _ _ (by decide) hs6 ?_; intro s7 hs7
  refine run_addcc _ _ _ _ (by decide) hs7 ?_; intro E0 K1 s8 hs8 e4 hk1
  refine run_addc _ _ _ _ _ _ (by decide) hs8
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hk1) ?_
  intro _ _ _ _ E1 K2 s9 hs9 e5 hk2
  refine run_addc _ _ _ _ _ _ (by decide) hs9
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hk2) ?_
  intro _ _ _ _ E2 K3 s10 hs10 e6 hk3
  refine run_addc _ _ _ _ _ _ (by decide) hs10
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hk3) ?_
  intro _ _ _ _ E3 K4 s11 hs11 e7 _
  refine (pass2_run hs11).mono ?_
  rintro R' ⟨hv, hf⟩
  refine ⟨?_, fun r hr => ?_⟩
  · have hfl := mul_small_toNat (R a4) 38 (by decide) h4
    have hfl2 := mul_small_toNat CY 38 (by decide) (by omega)
    simp only [upd, ↓reduceIte, String.reduceEq, ha, hz] at e0 e1 e2 e3 e4 e5 e6 e7
    rw [hfl] at e0
    rw [hfl2] at e4
    rw [hv]
    simp only [limbs4, upd, ↓reduceIte, String.reduceEq]
    have := D0.isLt; have := D1.isLt; have := D2.isLt; have := D3.isLt
    have := E0.isLt; have := E1.isLt; have := E2.isLt; have := E3.isLt
    have := (R a0).isLt; have := (R a1).isLt; have := (R a2).isLt; have := (R a3).isLt
    have h1 : D0.toNat + 2 ^ 64 * D1.toNat + 2 ^ 128 * D2.toNat + 2 ^ 192 * D3.toNat
        + 2 ^ 256 * CY.toNat = (R a0).toNat + 2 ^ 64 * (R a1).toNat + 2 ^ 128 * (R a2).toNat
          + 2 ^ 192 * (R a3).toNat + 38 * (R a4).toNat := by omega
    have h2 : E0.toNat + 2 ^ 64 * E1.toNat + 2 ^ 128 * E2.toNat + 2 ^ 192 * E3.toNat
        + 2 ^ 256 * K4.toNat = D0.toNat + 2 ^ 64 * D1.toNat + 2 ^ 128 * D2.toNat
          + 2 ^ 192 * D3.toNat + 38 * CY.toNat := by omega
    exact fold_mod _ _ _ _ _ _ (by omega) (by omega) (by omega) h4 h1 h2
  · rw [hf r hr]
    simp only [fold5Writes, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [upd, hr, ↓reduceIte]

/-! ## The field blocks -/

/-- The input limbs `q0..q3` and `y0..y3` read the same in `R'` as in `R`. -/
def QYFrame (R' R : AStateR) : Prop :=
  limbs4 R' "q0" "q1" "q2" "q3" = limbs4 R "q0" "q1" "q2" "q3" ∧
    limbs4 R' "y0" "y1" "y2" "y3" = limbs4 R "y0" "y1" "y2" "y3"

/-- `feAddBlock` leaves `(x + y) mod p25519` in `z0..z3`. -/
theorem feAdd_run {R : AStateR} {s : RState64} (hs : SRr s R) :
    Reach (fun R' => limbs4 R' "z0" "z1" "z2" "z3"
        = (limbs4 R "q0" "q1" "q2" "q3" + limbs4 R "y0" "y1" "y2" "y3") % p25519
      ∧ QYFrame R' R) (runRBlock64 s (lowerRBlock64 feAddBlock)) := by
  unfold feAddBlock
  simp only [List.cons_append, List.nil_append, lowerRBlock64_cons]
  refine run_addcc _ _ _ _ (by decide) hs ?_; intro D0 C1 s1 hs1 e0 hc1
  refine run_addc _ _ _ _ _ _ (by decide) hs1
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc1) ?_
  intro _ _ _ _ D1 C2 s2 hs2 e1 hc2
  refine run_addc _ _ _ _ _ _ (by decide) hs2
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc2) ?_
  intro _ _ _ _ D2 C3 s3 hs3 e2 hc3
  refine run_addc _ _ _ _ _ _ (by decide) hs3
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hc3) ?_
  intro _ _ _ _ D3 C4 s4 hs4 e3 hc4
  refine (fold5_run (by decide) hs4
    (by simp only [upd, ↓reduceIte, String.reduceEq]; omega)).mono ?_
  rintro R' ⟨hv, hf⟩
  refine ⟨?_, ?_⟩
  · rw [hv]; congr 1
    simp only [limbs4, upd, ↓reduceIte, String.reduceEq] at e1 e2 e3 ⊢
    omega
  · simp only [QYFrame, limbs4, hf "q0" (by decide), hf "q1" (by decide),
      hf "q2" (by decide), hf "q3" (by decide), hf "y0" (by decide), hf "y1" (by decide),
      hf "y2" (by decide), hf "y3" (by decide), upd, ↓reduceIte, String.reduceEq, and_self]

/-- `feSubBlock` leaves `(x + 2·p25519 − y) mod p25519` in `z0..z3` when
    `y ≤ x + 2·p25519`. -/
theorem feSub_run {R : AStateR} {s : RState64} (hs : SRr s R)
    (hy : limbs4 R "y0" "y1" "y2" "y3" ≤ limbs4 R "q0" "q1" "q2" "q3" + 2 * p25519) :
    Reach (fun R' => limbs4 R' "z0" "z1" "z2" "z3"
        = (limbs4 R "q0" "q1" "q2" "q3" + 2 * p25519 - limbs4 R "y0" "y1" "y2" "y3")
            % p25519
      ∧ QYFrame R' R) (runRBlock64 s (lowerRBlock64 feSubBlock)) := by
  have hz : (R "zero").toNat = 0 := by rw [SRr_zero hs]; rfl
  unfold feSubBlock
  simp only [List.cons_append, List.nil_append, lowerRBlock64_cons]
  refine run_li _ _ (by decide) hs ?_; intro s1 hs1
  refine run_li _ _ (by decide) hs1 ?_; intro s2 hs2
  refine run_li _ _ (by decide) hs2 ?_; intro s3 hs3
  refine run_li _ _ (by decide) hs3 ?_; intro s4 hs4
  refine run_addcc _ _ _ _ (by decide) hs4 ?_; intro S0 F1 s5 hs5 e0 hf1
  refine run_addc _ _ _ _ _ _ (by decide) hs5
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hf1) ?_
  intro _ _ _ _ S1 F2 s6 hs6 e1 hf2
  refine run_addc _ _ _ _ _ _ (by decide) hs6
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hf2) ?_
  intro _ _ _ _ S2 F3 s7 hs7 e2 hf3
  refine run_addc _ _ _ _ _ _ (by decide) hs7
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hf3) ?_
  intro _ _ _ _ S3 S4 s8 hs8 e3 hs4c
  refine run_subbb _ _ _ _ (by decide) hs8 ?_; intro A0 G1 s9 hs9 g0 hg1
  refine run_subb _ _ _ _ _ _ (by decide) hs9
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hg1) ?_
  intro _ _ _ _ A1 G2 s10 hs10 g1 hg2
  refine run_subb _ _ _ _ _ _ (by decide) hs10
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hg2) ?_
  intro _ _ _ _ A2 G3 s11 hs11 g2 hg3
  refine run_subb _ _ _ _ _ _ (by decide) hs11
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hg3) ?_
  intro _ _ _ _ A3 G4 s12 hs12 g3 hg4
  refine run_subb _ _ _ _ _ _ (by decide) hs12
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hg4) ?_
  intro _ _ _ _ A4 GF s13 hs13 g4 _
  simp only [upd, ↓reduceIte, String.reduceEq, hz] at e0 e1 e2 e3 g0 g1 g2 g3 g4
  have hS := chain_add4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e0 e1 e2 e3
  have hT : (BitVec.ofNat 64 0xffffffffffffffda).toNat
      + 2 ^ 64 * (BitVec.ofNat 64 0xffffffffffffffff).toNat
      + 2 ^ 128 * (BitVec.ofNat 64 0xffffffffffffffff).toNat
      + 2 ^ 192 * (BitVec.ofNat 64 0xffffffffffffffff).toNat = 2 * p25519 := by
    rw [← two_p25519_limbs]; rfl
  rw [hT] at hS
  have hA := chain_sub5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl g0 g1 g2 g3 g4
  rw [hS] at hA
  have hAlt := limbs5_lt A0 A1 A2 A3 A4
  unfold limbs4 at hy
  obtain ⟨hGF, hAeq⟩ := sub_no_borrow _ _ _ _ hAlt hy hA
  have hA4 : A4.toNat ≤ 1 :=
    top_le_one _ _ _ (limbs4_lt R "q0" "q1" "q2" "q3") (by rw [hAeq]; exact Nat.sub_le _ _)
  refine (fold5_run (by decide) hs13
    (by simp only [upd, ↓reduceIte]; exact Nat.lt_of_le_of_lt hA4 (by decide))).mono ?_
  rintro R' ⟨hv, hf⟩
  refine ⟨?_, ?_⟩
  · rw [hv]; congr 1
  · simp only [QYFrame, limbs4, hf "q0" (by decide), hf "q1" (by decide),
      hf "q2" (by decide), hf "q3" (by decide), hf "y0" (by decide), hf "y1" (by decide),
      hf "y2" (by decide), hf "y3" (by decide), upd, ↓reduceIte, String.reduceEq, and_self]

/-- `feMul121666Block` leaves `121666 · x mod p25519` in `z0..z3`. -/
theorem feMul121666_run {R : AStateR} {s : RState64} (hs : SRr s R) :
    Reach (fun R' => limbs4 R' "z0" "z1" "z2" "z3"
        = 121666 * limbs4 R "q0" "q1" "q2" "q3" % p25519
      ∧ QYFrame R' R) (runRBlock64 s (lowerRBlock64 feMul121666Block)) := by
  unfold feMul121666Block
  simp only [List.cons_append, List.nil_append, lowerRBlock64_cons]
  refine run_li _ _ (by decide) hs ?_; intro s1 hs1
  refine run_mul _ _ _ (by decide) hs1 ?_; intro s2 hs2
  refine run_mulhu _ _ _ (by decide) hs2 ?_; intro s3 hs3
  refine run_mul _ _ _ (by decide) hs3 ?_; intro s4 hs4
  refine run_mulhu _ _ _ (by decide) hs4 ?_; intro s5 hs5
  refine run_mul _ _ _ (by decide) hs5 ?_; intro s6 hs6
  refine run_mulhu _ _ _ (by decide) hs6 ?_; intro s7 hs7
  refine run_mul _ _ _ (by decide) hs7 ?_; intro s8 hs8
  refine run_mulhu _ _ _ (by decide) hs8 ?_; intro s9 hs9
  refine run_mov _ _ (by decide) hs9 ?_; intro s10 hs10
  refine run_addcc _ _ _ _ (by decide) hs10 ?_; intro A1 P1 s11 hs11 e1 hp1
  refine run_addc _ _ _ _ _ _ (by decide) hs11
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hp1) ?_
  intro _ _ _ _ A2 P2 s12 hs12 e2 hp2
  refine run_addc _ _ _ _ _ _ (by decide) hs12
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hp2) ?_
  intro _ _ _ _ A3 P3 s13 hs13 e3 hp3
  refine run_addcc _ _ _ _ (by decide) hs13 ?_; intro A4 P4 s14 hs14 e4 _
  simp only [upd, ↓reduceIte, String.reduceEq] at e1 e2 e3 e4
  have hk : (BitVec.ofNat 64 121666).toNat = 121666 := rfl
  have r0 := mul_mulhu_recompose (R "q0") (BitVec.ofNat 64 121666)
  have r1 := mul_mulhu_recompose (R "q1") (BitVec.ofNat 64 121666)
  have r2 := mul_mulhu_recompose (R "q2") (BitVec.ofNat 64 121666)
  have r3 := mul_mulhu_recompose (R "q3") (BitVec.ofNat 64 121666)
  simp only [hk] at r0 r1 r2 r3 e1 e2 e3 e4
  obtain ⟨ha4, hval⟩ := mul121666_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (R "q3").isLt A4.isLt r0 r1 r2 r3 e1 e2 e3 e4 hp3
  refine (fold5_run (by decide) hs14
    (by simp only [upd, ↓reduceIte]; exact ha4)).mono ?_
  rintro R' ⟨hv, hf⟩
  refine ⟨?_, ?_⟩
  · rw [hv]; congr 1
  · simp only [QYFrame, limbs4, hf "q0" (by decide), hf "q1" (by decide),
      hf "q2" (by decide), hf "q3" (by decide), hf "y0" (by decide), hf "y1" (by decide),
      hf "y2" (by decide), hf "y3" (by decide), upd, ↓reduceIte, String.reduceEq, and_self]

/-! ## The closed statements -/

/-- The run lemmas read at a machine state's own register map. -/
theorem reach_get {P : AStateR → Prop} {t : RState64} (h : Reach P t) : P t.get := by
  obtain ⟨R', hs', hP⟩ := h
  rwa [show t.get = R' from funext hs']

/-- **`feAddBlock` computes the field sum.** For every machine state, running the lowered
    block leaves `(x + y) mod p25519` in `z0..z3`, with `x` the limbs in `q0..q3` and `y`
    the limbs in `y0..y3`. -/
theorem feAdd_correct (s : RState64) :
    limbs4 (runRBlock64 s (lowerRBlock64 feAddBlock)).get "z0" "z1" "z2" "z3"
      = (limbs4 s.get "q0" "q1" "q2" "q3" + limbs4 s.get "y0" "y1" "y2" "y3") % p25519 :=
  (reach_get (feAdd_run (SRr_self s))).1

/-- **`feSubBlock` computes the field difference** when `y ≤ x + 2·p25519`. -/
theorem feSub_correct (s : RState64)
    (hy : limbs4 s.get "y0" "y1" "y2" "y3" ≤ limbs4 s.get "q0" "q1" "q2" "q3" + 2 * p25519) :
    limbs4 (runRBlock64 s (lowerRBlock64 feSubBlock)).get "z0" "z1" "z2" "z3"
      = (limbs4 s.get "q0" "q1" "q2" "q3" + 2 * p25519 - limbs4 s.get "y0" "y1" "y2" "y3")
          % p25519 :=
  (reach_get (feSub_run (SRr_self s) hy)).1

/-- **`feMul121666Block` computes the product by `121666`.** -/
theorem feMul121666_correct (s : RState64) :
    limbs4 (runRBlock64 s (lowerRBlock64 feMul121666Block)).get "z0" "z1" "z2" "z3"
      = 121666 * limbs4 s.get "q0" "q1" "q2" "q3" % p25519 :=
  (reach_get (feMul121666_run (SRr_self s))).1

theorem p25519_pos : 0 < p25519 := by rw [p25519_eq]; decide

/-- `feAdd_correct` in `ZMod p25519`: the result is canonical and is `x + y`. -/
theorem feAdd_correct_zmod (s : RState64) :
    limbs4 (runRBlock64 s (lowerRBlock64 feAddBlock)).get "z0" "z1" "z2" "z3" < p25519 ∧
      ((limbs4 (runRBlock64 s (lowerRBlock64 feAddBlock)).get "z0" "z1" "z2" "z3" : Nat)
          : ZMod p25519)
        = (limbs4 s.get "q0" "q1" "q2" "q3" : ZMod p25519)
          + (limbs4 s.get "y0" "y1" "y2" "y3" : ZMod p25519) := by
  rw [feAdd_correct]
  exact ⟨Nat.mod_lt _ p25519_pos, by rw [ZMod.natCast_mod, Nat.cast_add]⟩

/-- `feSub_correct` in `ZMod p25519`: the result is canonical and is `x − y`. -/
theorem feSub_correct_zmod (s : RState64)
    (hy : limbs4 s.get "y0" "y1" "y2" "y3" ≤ limbs4 s.get "q0" "q1" "q2" "q3" + 2 * p25519) :
    limbs4 (runRBlock64 s (lowerRBlock64 feSubBlock)).get "z0" "z1" "z2" "z3" < p25519 ∧
      ((limbs4 (runRBlock64 s (lowerRBlock64 feSubBlock)).get "z0" "z1" "z2" "z3" : Nat)
          : ZMod p25519)
        = (limbs4 s.get "q0" "q1" "q2" "q3" : ZMod p25519)
          - (limbs4 s.get "y0" "y1" "y2" "y3" : ZMod p25519) := by
  rw [feSub_correct s hy]
  refine ⟨Nat.mod_lt _ p25519_pos, ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_sub hy, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
    mul_zero, add_zero]

/-- `feMul121666_correct` in `ZMod p25519`: the result is canonical and is `121666 · x`. -/
theorem feMul121666_correct_zmod (s : RState64) :
    limbs4 (runRBlock64 s (lowerRBlock64 feMul121666Block)).get "z0" "z1" "z2" "z3"
        < p25519 ∧
      ((limbs4 (runRBlock64 s (lowerRBlock64 feMul121666Block)).get "z0" "z1" "z2" "z3"
          : Nat) : ZMod p25519)
        = 121666 * (limbs4 s.get "q0" "q1" "q2" "q3" : ZMod p25519) := by
  rw [feMul121666_correct]
  refine ⟨Nat.mod_lt _ p25519_pos, ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat]

/-! ## The `CorresR` squares -/

/-- The abstract state of the field blocks: the values in `q0..q3`, `y0..y3`, `z0..z3`. -/
structure AFe where
  /-- The value in `q0..q3`. -/
  x : Nat
  /-- The value in `y0..y3`. -/
  y : Nat
  /-- The value in `z0..z3`. -/
  z : Nat

/-- `SRfe`: the machine's `q`, `y` and `z` limbs read as the abstract `x`, `y`, `z`. -/
def SRfe (s : RState64) (a : AFe) : Prop :=
  limbs4 s.get "q0" "q1" "q2" "q3" = a.x ∧ limbs4 s.get "y0" "y1" "y2" "y3" = a.y ∧
    limbs4 s.get "z0" "z1" "z2" "z3" = a.z

/-- `SRfe` has a witness, at the trivial guard. -/
theorem srfe_satisfiable : ∃ s a, SRfe s a ∧ True :=
  ⟨{ regs := fun _ => 0 }, ⟨0, 0, 0⟩, by simp [SRfe, limbs4, RState64.get], trivial⟩

/-- A run lemma with frame gives a `CorresR` square over `SRfe` for the step that
    replaces `z` by `f x y`. -/
theorem corresR_of_run {P : AFe → Prop} {f : Nat → Nat → Nat} {c : List RInst64}
    (h : ∀ (s : RState64), P ⟨limbs4 s.get "q0" "q1" "q2" "q3",
      limbs4 s.get "y0" "y1" "y2" "y3", 0⟩ →
      Reach (fun R' => limbs4 R' "z0" "z1" "z2" "z3"
          = f (limbs4 s.get "q0" "q1" "q2" "q3") (limbs4 s.get "y0" "y1" "y2" "y3")
        ∧ QYFrame R' s.get) (runRBlock64 s c))
    (hP : ∀ a, P a ↔ P ⟨a.x, a.y, 0⟩) :
    CorresR SRfe P (fun a => ⟨a.x, a.y, f a.x a.y⟩) c := by
  intro s a ⟨hx, hy, _⟩ hPa
  have hP0 : P ⟨limbs4 s.get "q0" "q1" "q2" "q3", limbs4 s.get "y0" "y1" "y2" "y3", 0⟩ := by
    rw [hx, hy]; exact (hP a).mp hPa
  obtain ⟨hz, hq, hy'⟩ := reach_get (h s hP0)
  exact ⟨by rw [hq, hx], by rw [hy', hy], by rw [hz, hx, hy]⟩

/-- **`feAddBlock` refines `z := (x + y) mod p25519`.** -/
theorem feAdd_corresR :
    CorresR SRfe (fun _ => True) (fun a => ⟨a.x, a.y, (a.x + a.y) % p25519⟩)
      (lowerRBlock64 feAddBlock) :=
  corresR_of_run (f := fun x y => (x + y) % p25519)
    (fun s _ => feAdd_run (SRr_self s)) (fun _ => Iff.rfl)

/-- **`feSubBlock` refines `z := (x + 2·p25519 − y) mod p25519`** from `y ≤ x + 2·p25519`. -/
theorem feSub_corresR :
    CorresR SRfe (fun a => a.y ≤ a.x + 2 * p25519)
      (fun a => ⟨a.x, a.y, (a.x + 2 * p25519 - a.y) % p25519⟩) (lowerRBlock64 feSubBlock) :=
  corresR_of_run (f := fun x y => (x + 2 * p25519 - y) % p25519)
    (fun s h => feSub_run (SRr_self s) h) (fun _ => Iff.rfl)

/-- **`feMul121666Block` refines `z := 121666 · x mod p25519`.** -/
theorem feMul121666_corresR :
    CorresR SRfe (fun _ => True) (fun a => ⟨a.x, a.y, 121666 * a.x % p25519⟩)
      (lowerRBlock64 feMul121666Block) :=
  corresR_of_run (f := fun x _ => 121666 * x % p25519)
    (fun s _ => feMul121666_run (SRr_self s)) (fun _ => Iff.rfl)

/-! ## The conditional swap -/

/-- **`cswapBlock` swaps when `swap` holds `1`.** For every machine state whose `swap`
    register holds `0` or `1`, running the lowered block leaves in `a0..a3` the old
    `b0..b3` and in `b0..b3` the old `a0..a3` when it holds `1`, and leaves both
    unchanged when it holds `0`. -/
theorem cswap_correct (s : RState64) (hsw : (s.get "swap").toNat ≤ 1) :
    limbs4 (runRBlock64 s (lowerRBlock64 cswapBlock)).get "a0" "a1" "a2" "a3"
        = (if (s.get "swap").toNat = 1 then limbs4 s.get "b0" "b1" "b2" "b3"
            else limbs4 s.get "a0" "a1" "a2" "a3") ∧
      limbs4 (runRBlock64 s (lowerRBlock64 cswapBlock)).get "b0" "b1" "b2" "b3"
        = (if (s.get "swap").toNat = 1 then limbs4 s.get "a0" "a1" "a2" "a3"
            else limbs4 s.get "b0" "b1" "b2" "b3") := by
  refine reach_get (P := fun R' =>
    limbs4 R' "a0" "a1" "a2" "a3" = (if (s.get "swap").toNat = 1
      then limbs4 s.get "b0" "b1" "b2" "b3" else limbs4 s.get "a0" "a1" "a2" "a3") ∧
    limbs4 R' "b0" "b1" "b2" "b3" = (if (s.get "swap").toNat = 1
      then limbs4 s.get "a0" "a1" "a2" "a3" else limbs4 s.get "b0" "b1" "b2" "b3")) ?_
  have hs := SRr_self s
  unfold cswapBlock
  simp only [lowerRBlock64_cons, lowerRBlock64_nil]
  refine run_mov _ _ (by decide) hs ?_; intro t1 ht1
  refine run_csub _ _ _ _ _ _ (by decide) ht1
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hsw) ?_
  intro _ _ _ _ X0 t2 ht2 x0
  refine run_csub _ _ _ _ _ _ (by decide) ht2
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hsw) ?_
  intro _ _ _ _ Y0 t3 ht3 y0
  refine run_mov _ _ (by decide) ht3 ?_; intro t4 ht4
  refine run_csub _ _ _ _ _ _ (by decide) ht4
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hsw) ?_
  intro _ _ _ _ X1 t5 ht5 x1
  refine run_csub _ _ _ _ _ _ (by decide) ht5
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hsw) ?_
  intro _ _ _ _ Y1 t6 ht6 y1
  refine run_mov _ _ (by decide) ht6 ?_; intro t7 ht7
  refine run_csub _ _ _ _ _ _ (by decide) ht7
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hsw) ?_
  intro _ _ _ _ X2 t8 ht8 x2
  refine run_csub _ _ _ _ _ _ (by decide) ht8
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hsw) ?_
  intro _ _ _ _ Y2 t9 ht9 y2
  refine run_mov _ _ (by decide) ht9 ?_; intro t10 ht10
  refine run_csub _ _ _ _ _ _ (by decide) ht10
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hsw) ?_
  intro _ _ _ _ X3 t11 ht11 x3
  refine run_csub _ _ _ _ _ _ (by decide) ht11
    (by simpa only [upd, ↓reduceIte, String.reduceEq] using hsw) ?_
  intro _ _ _ _ Y3 t12 ht12 y3
  refine run_nil ht12 ⟨?_, ?_⟩ <;>
  · simp only [upd, ↓reduceIte, String.reduceEq] at x0 y0 x1 y1 x2 y2 x3 y3
    simp only [limbs4, upd, ↓reduceIte, String.reduceEq]
    subst x0 y0 x1 y1 x2 y2 x3 y3
    split <;> rfl

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519AddSubProof.feSub_correct_zmod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms feSub_correct_zmod

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519AddSubProof.cswap_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cswap_correct

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519AddSubProof
