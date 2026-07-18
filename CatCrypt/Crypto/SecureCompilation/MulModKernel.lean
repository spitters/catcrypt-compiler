/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.AddModKernel
import Mathlib

/-!
# Field multiplication `(a · b) mod p` via Barrett reduction

The capstone field kernel: 64-bit prime-field multiplication. For `a, b < p < 2^32`
the product `a·b < 2^64`, reduced mod `p` by Barrett's method — estimate the
quotient `q = ⌊a·b · μ / 2^64⌋` with the precomputed `μ = ⌊2^64/p⌋` (one `mulhi`),
form `r = a·b − q·p`, and finish with the branchless conditional subtract from
`FieldReduceIdioms` (Barrett guarantees `r ∈ [0, 2p)`).

`barrett_bound` is the number-theoretic core (`q·p ≤ x ∧ x − q·p < 2p`); the kernel
inherits the existing alphabet (`mul`, `mulhi`, `sub`, the conditional subtract) and
both backends. The end-to-end value-correctness (`result.toNat = (a·b) mod p`)
composes `barrett_bound` with `bCondSub_toNat`; the `denote = bCondSub r p` step over
the `mulhi` register is the remaining assembly (a `bv_decide` factoring of the
conditional-subtract block over an abstract remainder), pending here.
-/

namespace CatCrypt.Crypto.SecureCompilation.MulModKernel

open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms

/-- `n < (n / m + 1) * m` for `0 < m`. -/
private theorem lt_div_add_one_mul (n m : Nat) (hm : 0 < m) : n < (n / m + 1) * m := by
  have h1 := Nat.div_add_mod n m
  have h2 := Nat.mod_lt n hm
  nlinarith [h1, h2]

/-- **Barrett bound.** With `μ = ⌊2^64/p⌋` and `q = ⌊x·μ / 2^64⌋`, the estimate
    satisfies `q·p ≤ x` and `x − q·p < 2p` — so one conditional subtract reduces. -/
theorem barrett_bound (p x : Nat) (hp : 0 < p) (hp32 : p < 2 ^ 32) (hx : x < 2 ^ 64) :
    (x * (2 ^ 64 / p) / 2 ^ 64) * p ≤ x ∧
      x - (x * (2 ^ 64 / p) / 2 ^ 64) * p < 2 * p := by
  set mu := 2 ^ 64 / p with hmu
  set q := x * mu / 2 ^ 64 with hq
  have hmu0 : 0 < mu := Nat.div_pos (by omega) hp
  have hqpx : q * p ≤ x := by
    have a1 : q * 2 ^ 64 ≤ x * mu := Nat.div_mul_le_self _ _
    have a2 : mu * p ≤ 2 ^ 64 := Nat.div_mul_le_self _ _
    nlinarith [a1, a2, Nat.zero_le x, Nat.zero_le q, Nat.zero_le mu]
  refine ⟨hqpx, ?_⟩
  have h3 : 2 ^ 64 < (mu + 1) * p := lt_div_add_one_mul _ p hp
  have h4 : x * mu < (q + 1) * 2 ^ 64 := lt_div_add_one_mul _ _ (by norm_num)
  have h5 : q + 1 ≤ mu := by
    have hqm : q < mu := Nat.div_lt_of_lt_mul (by nlinarith [hx, hmu0])
    omega
  have step1 : x * mu < (q + 1) * ((mu + 1) * p) :=
    lt_of_lt_of_le h4 (Nat.mul_le_mul_left (q + 1) (le_of_lt h3))
  have step2 : (q + 1) * ((mu + 1) * p) ≤ (q * p + 2 * p) * mu := by
    nlinarith [Nat.mul_le_mul_right p h5, hp, Nat.zero_le q, Nat.zero_le mu]
  have key : x * mu < (q * p + 2 * p) * mu := lt_of_lt_of_le step1 step2
  have hlt : x < q * p + 2 * p := lt_of_mul_lt_mul_right key (Nat.zero_le mu)
  omega

open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-- The branchless conditional-subtract block over input registers `r`, `pc`
    (`ones` = all-ones, `zero` = 0). Factored out so its `bv_decide` runs over an
    *abstract* remainder, free of the `mulhi` term. -/
def condSubBlock : RegProg :=
  [ .sub "d" "r" "pc", .eor "rxp" "r" "pc", .eor "nrxp" "rxp" "ones", .and "t1" "nrxp" "d",
    .eor "nr" "r" "ones", .and "t2" "nr" "pc", .orr "bor0" "t2" "t1", .shrI "bor" "bor0" 63,
    .sub "mask" "zero" "bor", .and "r1" "r" "mask", .eor "nmask" "mask" "ones",
    .and "r2" "d" "nmask", .orr "res" "r1" "r2" ]

theorem condSubBlock_denote (env : Env) (hones : env "ones" = 0xFFFFFFFFFFFFFFFF)
    (hzero : env "zero" = 0) :
    (RegProg.denotePure condSubBlock env) "res" = bCondSub (env "r") (env "pc") := by
  simp only [condSubBlock, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure,
    Env.set, Env.get, bCondSub, bSltu, String.reduceEq, reduceIte, hones, hzero]
  bv_decide

/-- The prefix computing the Barrett remainder `r = a·b − ⌊a·b·μ/2^64⌋·p` and the
    constants `ones`/`zero` the block needs. -/
def mulPrefix (p : Nat) : RegProg :=
  [ .mul "x" "a" "b",
    .loadImm "muc" (2 ^ 64 / p),
    .umulh "q" "x" "muc",
    .loadImm "pc" p,
    .mul "qp" "q" "pc",
    .sub "r" "x" "qp",
    .loadImm "ones" 0xFFFFFFFFFFFFFFFF,
    .loadImm "zero" 0 ]

/-- Field multiplication `(a · b) mod p`: the Barrett prefix then the conditional
    subtract. `μ = ⌊2^64/p⌋` via `loadImm`. -/
def mulmodProg (p : Nat) : RegProg := mulPrefix p ++ condSubBlock

/-- The result register holds the conditional subtract of the Barrett remainder. -/
theorem mulmodProg_denote (p : Nat) (env : Env) :
    (RegProg.denotePure (mulmodProg p) env) "res"
      = bCondSub
          ((env "a" * env "b") -
            BitVec.ofNat 64 (((env "a" * env "b").toNat *
                (BitVec.ofNat 64 (2 ^ 64 / p)).toNat) >>> 64) * BitVec.ofNat 64 p)
          (BitVec.ofNat 64 p) := by
  rw [mulmodProg, RegProg.denotePure_append,
      condSubBlock_denote _
        (by simp [mulPrefix, RegProg.denotePure, evalRegStmtPure, Env.set, Env.get])
        (by simp [mulPrefix, RegProg.denotePure, evalRegStmtPure, Env.set, Env.get])]
  congr 1 <;>
    simp [mulPrefix, RegProg.denotePure, evalRegStmtPure, Env.set, Env.get]

/-- **Field-arithmetic correctness.** For `a, b < p` (and `1 < p < 2^32`) the kernel
    returns `(a · b) mod p` — `barrett_bound` bounds the remainder `< 2p`, the
    branchless conditional subtract reduces it, and the `mulhi` register realises the
    Barrett quotient `⌊a·b·μ/2^64⌋`. -/
theorem mulmodProg_toNat (p : Nat) (env : Env) (hp1 : 1 < p) (hp32 : p < 2 ^ 32)
    (ha : (env "a").toNat < p) (hb : (env "b").toNat < p) :
    ((RegProg.denotePure (mulmodProg p) env) "res").toNat
      = ((env "a").toNat * (env "b").toNat) % p := by
  rw [mulmodProg_denote]
  have hp0 : 0 < p := by omega
  have hABlt : (env "a").toNat * (env "b").toNat < 2 ^ 64 := by
    have hA : (env "a").toNat ≤ 2 ^ 32 - 1 := by omega
    have hB : (env "b").toNat ≤ 2 ^ 32 - 1 := by omega
    calc (env "a").toNat * (env "b").toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul hA hB
      _ < 2 ^ 64 := by norm_num
  have hXt : (env "a" * env "b").toNat = (env "a").toNat * (env "b").toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hABlt]
  have hmuct : (BitVec.ofNat 64 (2 ^ 64 / p)).toNat = 2 ^ 64 / p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.div_lt_self (by norm_num) hp1)]
  have hpct : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hqpx, hr2p⟩ := barrett_bound p ((env "a").toNat * (env "b").toNat) hp0 hp32 hABlt
  have hQlt : (env "a").toNat * (env "b").toNat * (2 ^ 64 / p) / 2 ^ 64 < 2 ^ 64 :=
    Nat.div_lt_of_lt_mul (by nlinarith [hABlt, Nat.div_lt_self (show (0:Nat) < 2 ^ 64 by norm_num) hp1])
  have huml : (BitVec.ofNat 64 (((env "a" * env "b").toNat *
      (BitVec.ofNat 64 (2 ^ 64 / p)).toNat) >>> 64)).toNat
      = (env "a").toNat * (env "b").toNat * (2 ^ 64 / p) / 2 ^ 64 := by
    rw [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, hXt, hmuct, Nat.mod_eq_of_lt hQlt]
  have hqpt : (BitVec.ofNat 64 (((env "a" * env "b").toNat *
      (BitVec.ofNat 64 (2 ^ 64 / p)).toNat) >>> 64) * BitVec.ofNat 64 p).toNat
      = (env "a").toNat * (env "b").toNat * (2 ^ 64 / p) / 2 ^ 64 * p := by
    rw [BitVec.toNat_mul, huml, hpct, Nat.mod_eq_of_lt (by omega)]
  have hRt : (env "a" * env "b" - BitVec.ofNat 64 (((env "a" * env "b").toNat *
      (BitVec.ofNat 64 (2 ^ 64 / p)).toNat) >>> 64) * BitVec.ofNat 64 p).toNat
      = (env "a").toNat * (env "b").toNat
        - (env "a").toNat * (env "b").toNat * (2 ^ 64 / p) / 2 ^ 64 * p := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hqpt, hXt]; exact hqpx)), hqpt, hXt]
  rw [bCondSub_toNat _ _ (by rw [hpct]; omega) (by rw [hRt, hpct]; omega), hRt, hpct]
  conv_rhs => rw [show (env "a").toNat * (env "b").toNat
    = ((env "a").toNat * (env "b").toNat
        - (env "a").toNat * (env "b").toNat * (2 ^ 64 / p) / 2 ^ 64 * p)
      + (env "a").toNat * (env "b").toNat * (2 ^ 64 / p) / 2 ^ 64 * p from by omega]
  rw [Nat.add_mul_mod_self_right]

/-- **High-level spec link.** The kernel computes `ZMod p` field multiplication. -/
theorem mulmodProg_zmod (p : Nat) [NeZero p] (env : Env) (hp1 : 1 < p) (hp32 : p < 2 ^ 32)
    (ha : (env "a").toNat < p) (hb : (env "b").toNat < p) :
    ((RegProg.denotePure (mulmodProg p) env) "res").toNat
      = (((env "a").toNat : ZMod p) * ((env "b").toNat : ZMod p)).val := by
  rw [mulmodProg_toNat p env hp1 hp32 ha hb, ← Nat.cast_mul, ZMod.val_natCast]

/-- The field-multiply kernel compiles to AArch64 (generic keystone). -/
theorem mulmodProg_arm (p : Nat) (s : BState) :
    runBBlock s (lowerBBlock (regToBOp (mulmodProg p))) = armTarget.denote (mulmodProg p) s :=
  regToBOp_denote (mulmodProg p) s

/-- …and to RISC-V. -/
theorem mulmodProg_riscv (p : Nat) (s : RState64) :
    runRBlock64 s (lowerRBlock64 (regToROp (mulmodProg p))) = rvTarget.denote (mulmodProg p) s :=
  regToROp_denote (mulmodProg p) s

end CatCrypt.Crypto.SecureCompilation.MulModKernel
