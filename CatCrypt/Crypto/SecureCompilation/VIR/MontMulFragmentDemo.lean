/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# Multi-limb widening-multiply + carry-propagation demonstration (task #477)

#474 found the linear-jasmin `Com jasminDialect` to be **carry-free with no
widening multiply**: its `JasminBinOp` alphabet is `add/sub/mul/and/or/xor/
shl/shr`, where `mul` keeps only the low `w` bits. A multi-limb Montgomery /
pairing-field multiply — the `MULX` (64×64→128) + dual `ADCX`/`ADOX` carry-chain
idiom — could not be expressed, blocking the owned register-allocation path for
those kernels.

Task #477 added three single-output ops to the dialect whose denotations are the
pure (flag-free) effects of that idiom, **ported from the owned x86 model**
(`X86Backend/Model.lean`):

* `mulhi w`     — `mulHiW`     = high word of `a * b`        (= `Model.mulHi`)
* `addCarryLo w`— `addCarryWord` = `a + b + cin`            (= `Model.step .adcx` data)
* `addCarryHi w`— `carryOutBit`  = carry-out of `a + b + cin`(= `Model.addCarry`)

This file is the *demonstration* that the dialect can now express the
widening-mul + carry-propagated add that #474 was blocked on. It builds the
`mpn_mul_1` / Montgomery inner kernel — a **2-limb × 1-limb** widening product
with full carry propagation — as `Com jasminDialect` programs, proves each
output limb's `Com.denote` equals the intended BitVec function, proves the
combined three-limb `Nat`-level product identity, and pins a **GMP** KAT
(reference limbs computed by `libgmp` in `/tmp/montref.c`, cross-checked with
`bc`; no fabricated vectors).

## The kernel

For `a = a0 + a1 · 2^64` and a single word `b`, the double-word product
`a · b` is the three-limb value `r0 + r1 · 2^64 + r2 · 2^128` where, writing
`a0·b = hi0 : lo0` and `a1·b = hi1 : lo1` (each a `MULX`):

```
r0 = lo0
(r1, c1) = lo1 + hi0          -- ADCX/ADOX:  addCarryWord / carryOutBit
r2       = hi1 + c1           -- ADCX/ADOX with the propagated carry
```

`r2` needs no further carry (a 2×1-limb product fits in three limbs), so the
top add is `addCarryWord hi1 0 c1`. Every arrow is one of the new ops; the two
`MULX`es are `(mulhi, regArith .mul)` pairs.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MontMulFragmentDemo

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## 1. Argument context and convenient variable references

The argument context is `[a0, a1, b]` (most-recent-binder-first De Bruijn, so
`a0 = .here`). All three are `reg 64`. -/

abbrev Γ : Ctxt jasminDialect := [.reg 64, .reg 64, .reg 64]

/-- `a0` (slot 0). -/ def va0 : Ctxt.Var Γ (.reg 64) := .here
/-- `a1` (slot 1). -/ def va1 : Ctxt.Var Γ (.reg 64) := .there .here
/-- `b`  (slot 2). -/ def vb  : Ctxt.Var Γ (.reg 64) := .there (.there .here)

/-! ## 2. The intended pure functions (over `BitVec 64`)

These are the spec the `Com`s must denote: exactly the `mulHiW` /
`addCarryWord` / `carryOutBit` compositions of the kernel above. -/

/-- Low word of `a0 * b`. -/
def lo0 (a0 b : BitVec 64) : BitVec 64 := a0 * b
/-- High word of `a0 * b` (`MULX` hi). -/
def hi0 (a0 b : BitVec 64) : BitVec 64 := mulHiW a0 b
/-- Low word of `a1 * b`. -/
def lo1 (a1 b : BitVec 64) : BitVec 64 := a1 * b
/-- High word of `a1 * b` (`MULX` hi). -/
def hi1 (a1 b : BitVec 64) : BitVec 64 := mulHiW a1 b

/-- Result limb 0. -/
def r0 (a0 b : BitVec 64) : BitVec 64 := lo0 a0 b
/-- The carry out of limb 1's add (`ADCX`/`ADOX` carry-out). -/
def c1 (a0 a1 b : BitVec 64) : BitVec 1 := carryOutBit (lo1 a1 b) (hi0 a0 b) 0
/-- Result limb 1 (`ADCX`/`ADOX` data: `lo1 + hi0 + 0`). -/
def r1 (a0 a1 b : BitVec 64) : BitVec 64 := addCarryWord (lo1 a1 b) (hi0 a0 b) 0
/-- Result limb 2 (`ADCX`/`ADOX` data: `hi1 + 0 + c1`). -/
def r2 (a0 a1 b : BitVec 64) : BitVec 64 := addCarryWord (hi1 a1 b) 0 (c1 a0 a1 b)

/-! ## 3. The `Com` programs

One `Com` per output limb, all over the shared argument context `Γ`. Each is a
straight-line let-chain in exactly the new ops (plus `regArith .mul` for the
low words and a `regConst 64 0` for the additive zero in `r2`). -/

/-- Limb 0: `r0 = lo0 = a0 * b`. (A single `regArith .mul`.) -/
def comR0 : Com jasminDialect Γ (.reg 64) :=
  .var (.mk (.regArith .mul 64) rfl (.cons va0 (.cons vb .nil)))
    (.ret .here)

/-- Limb 1: `r1 = lo1 + hi0` (the data word of an `ADCX`/`ADOX`).
    Binds `lo1 = a1*b`, `hi0 = mulhi a0 b`, then `addCarryLo lo1 hi0 0`,
    where the `0` carry-in is a `regConst 1 0`. -/
def comR1 : Com jasminDialect Γ (.reg 64) :=
  -- d0 := lo1 = a1 * b
  .var (.mk (.regArith .mul 64) rfl (.cons va1 (.cons vb .nil)))
  -- d1 := hi0 = mulhi a0 b      (vars shifted by one binder)
  (.var (.mk (.mulhi 64) rfl
            (.cons (.there va0) (.cons (.there vb) .nil)))
  -- d2 := cin0 : reg 1 = 0
  (.var (.mk (.regConst 1 0) rfl .nil)
  -- d3 := addCarryLo d0 d1 d2     (lo1 = .there .there .here, hi0 = .there .here, cin = .here)
  (.var (.mk (.addCarryLo 64) rfl
            (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))))
    (.ret .here))))

/-- Limb 2: `r2 = hi1 + 0 + c1` (the data word of the top `ADCX`/`ADOX`,
    consuming the carry-out of limb 1). Binds `lo1`, `hi0`, `cin0 = 0`,
    `c1 = addCarryHi lo1 hi0 cin0`, `hi1 = mulhi a1 b`, `zero = regConst 64 0`,
    then `addCarryLo hi1 zero c1`. -/
def comR2 : Com jasminDialect Γ (.reg 64) :=
  -- d0 := lo1 = a1 * b
  .var (.mk (.regArith .mul 64) rfl (.cons va1 (.cons vb .nil)))
  -- d1 := hi0 = mulhi a0 b
  (.var (.mk (.mulhi 64) rfl
            (.cons (.there va0) (.cons (.there vb) .nil)))
  -- d2 := cin0 : reg 1 = 0
  (.var (.mk (.regConst 1 0) rfl .nil)
  -- d3 := c1 = addCarryHi d0 d1 d2  (lo1 = .there .there .here, hi0 = .there .here, cin = .here)
  (.var (.mk (.addCarryHi 64) rfl
            (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))))
  -- d4 := hi1 = mulhi a1 b   (a1 is now at De Bruijn depth: Γ tail shifted by 4 binders)
  (.var (.mk (.mulhi 64) rfl
            (.cons (.there (.there (.there (.there va1))))
              (.cons (.there (.there (.there (.there vb)))) .nil)))
  -- d5 := zero : reg 64 = 0
  (.var (.mk (.regConst 64 0) rfl .nil)
  -- d6 := addCarryLo hi1 zero c1
  --   ctx = [d5(zero), d4(hi1), d3(c1), d2, d1, d0, a0, a1, b]
  --   hi1 = d4 = .there .here ; zero = d5 = .here ; c1 = d3 = .there .there .here
  (.var (.mk (.addCarryLo 64) rfl
            (.cons (.there .here)
              (.cons .here
                (.cons (.there (.there .here)) .nil))))
    (.ret .here)))))))

/-! ## 4. Denotation correctness (each limb's `Com` denotes its spec) -/

/-- The input valuation `⟨a0, a1, b⟩`. -/
def val (a0 a1 b : BitVec 64) : Ctxt.Valuation Γ :=
  .cons a0 (.cons a1 (.cons b .nil))

@[simp] theorem comR0_denote (a0 a1 b : BitVec 64) :
    comR0.denote (val a0 a1 b) = r0 a0 b := by
  rfl

@[simp] theorem comR1_denote (a0 a1 b : BitVec 64) :
    comR1.denote (val a0 a1 b) = r1 a0 a1 b := by
  rfl

@[simp] theorem comR2_denote (a0 a1 b : BitVec 64) :
    comR2.denote (val a0 a1 b) = r2 a0 a1 b := by
  rfl

/-! ## 5. The multi-limb product identity (`Nat` level)

The three limbs reassemble to the true double-word product
`(a0 + a1·2^64) · b`. This is the carry-propagation correctness #474 could not
state: it depends on `mulHiW` carrying the high half of each `MULX` and on
`addCarryWord`/`carryOutBit` threading the carry between limbs. -/

/-- The machine modulus is positive. -/
theorem q_pos : 0 < (2 : Nat) ^ 64 := Nat.pow_pos (by decide)

/-- `a.toNat * b.toNat < 2^64 * 2^64` for any two 64-bit words. -/
theorem prod_lt (a b : BitVec 64) : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 :=
  Nat.mul_lt_mul'' a.isLt b.isLt

/-- The high word of a 64×64 product is `< 2^64` (so the `ofNat` truncation in
    `mulHiW` is a no-op). -/
theorem mulHiW_lt (a b : BitVec 64) : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 :=
  Nat.div_lt_of_lt_mul (prod_lt a b)

/-- `(mulHiW a b).toNat = a.toNat * b.toNat / 2^64` (truncation no-op). -/
theorem mulHiW_toNat (a b : BitVec 64) :
    (mulHiW a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  simp only [mulHiW, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (mulHiW_lt a b)

/-- A single `MULX` reconstructs the full 128-bit product:
    `lo + hi · 2^64 = a · b` (as naturals). -/
theorem mulx_reconstruct (a b : BitVec 64) :
    (a * b).toNat + (mulHiW a b).toNat * 2 ^ 64 = a.toNat * b.toNat := by
  rw [mulHiW_toNat, BitVec.toNat_mul,
    Nat.mul_comm (a.toNat * b.toNat / 2 ^ 64) (2 ^ 64), Nat.add_comm]
  exact Nat.div_add_mod _ _

/-- The carry-out `c1` is the `2^64`-overflow bit of `lo1 + hi0`, and
    `r1 = (lo1 + hi0) mod 2^64`, so `r1 + c1·2^64 = lo1 + hi0`. -/
theorem r1_carry_split (a0 a1 b : BitVec 64) :
    (r1 a0 a1 b).toNat + (c1 a0 a1 b).toNat * 2 ^ 64
      = (lo1 a1 b).toNat + (hi0 a0 b).toNat := by
  have hlo := (lo1 a1 b).isLt
  have hhi := (hi0 a0 b).isLt
  have hq := q_pos
  have hz1 : BitVec.toNat (0 : BitVec 1) = 0 := rfl
  -- data word = (lo1+hi0) % 2^64 ; carry bit = 1 iff lo1+hi0 ≥ 2^64.
  have hword : (r1 a0 a1 b).toNat
      = ((lo1 a1 b).toNat + (hi0 a0 b).toNat) % 2 ^ 64 := by
    simp only [r1, addCarryWord, BitVec.toNat_add, BitVec.toNat_ofNat, hz1,
      Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
  have hbit : (c1 a0 a1 b).toNat
      = (if 2 ^ 64 ≤ (lo1 a1 b).toNat + (hi0 a0 b).toNat then 1 else 0) := by
    simp only [c1, carryOutBit, hz1, Nat.add_zero, ge_iff_le]
    by_cases h : 2 ^ 64 ≤ (lo1 a1 b).toNat + (hi0 a0 b).toNat
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]; rfl
  rw [hword, hbit]
  by_cases h : 2 ^ 64 ≤ (lo1 a1 b).toNat + (hi0 a0 b).toNat
  · rw [if_pos h]
    have hmod : ((lo1 a1 b).toNat + (hi0 a0 b).toNat) % 2 ^ 64
        = (lo1 a1 b).toNat + (hi0 a0 b).toNat - 2 ^ 64 := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]; omega
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]; omega

/-- The high word of a 64×64 product is at most `2^64 - 2` (so `hi1 + c1` with
    `c1 ≤ 1` never wraps): `a·b ≤ (2^64-1)^2`, and that quotient is `2^64 - 2`. -/
theorem mulHiW_le (a b : BitVec 64) : (mulHiW a b).toNat ≤ 2 ^ 64 - 2 := by
  rw [mulHiW_toNat]
  -- a*b ≤ (2^64-1)^2 < (2^64-1)·2^64, so a*b/2^64 < 2^64-1, i.e. ≤ 2^64-2.
  have ha : a.toNat ≤ 2 ^ 64 - 1 := by have := a.isLt; omega
  have hb : b.toNat ≤ 2 ^ 64 - 1 := by have := b.isLt; omega
  have hp : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul ha hb
  have hstrict : (2 ^ 64 - 1) * (2 ^ 64 - 1) < (2 ^ 64 - 1) * 2 ^ 64 :=
    (Nat.mul_lt_mul_left (show 0 < 2 ^ 64 - 1 by have := q_pos; omega)).mpr
      (show 2 ^ 64 - 1 < 2 ^ 64 by have := q_pos; omega)
  have hlt : a.toNat * b.toNat < (2 ^ 64 - 1) * 2 ^ 64 := Nat.lt_of_le_of_lt hp hstrict
  have hdiv : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 - 1 := by
    rw [Nat.mul_comm (2 ^ 64 - 1) (2 ^ 64)] at hlt
    exact Nat.div_lt_of_lt_mul hlt
  omega

/-- `r2` needs no further carry: `hi1 ≤ 2^64 - 2` (`mulHiW_le`) and `c1 ≤ 1`, so
    `hi1 + c1 < 2^64`. Hence `r2 = hi1 + c1` exactly (no top wrap). -/
theorem r2_no_wrap (a0 a1 b : BitVec 64) :
    (r2 a0 a1 b).toNat = (hi1 a1 b).toNat + (c1 a0 a1 b).toNat := by
  have hc : (c1 a0 a1 b).toNat ≤ 1 := by have := (c1 a0 a1 b).isLt; omega
  have hh : (hi1 a1 b).toNat ≤ 2 ^ 64 - 2 := mulHiW_le a1 b
  have h0 : ((0 : BitVec 64)).toNat = 0 := rfl
  have hcm : (c1 a0 a1 b).toNat % 2 ^ 64 = (c1 a0 a1 b).toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hhm : (hi1 a1 b).toNat % 2 ^ 64 = (hi1 a1 b).toNat :=
    Nat.mod_eq_of_lt (by omega)
  simp only [r2, addCarryWord, BitVec.toNat_add, BitVec.toNat_ofNat, h0, Nat.add_zero, hcm,
    hhm]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- **Multi-limb product identity.** The three limbs `r0, r1, r2` produced by the
    `Com` kernel reassemble to the true double-word product:

    `r0 + r1·2^64 + r2·2^128 = (a0 + a1·2^64) · b`.

    Proved from the per-`MULX` reconstruction (`mulx_reconstruct`) and the
    carry split (`r1_carry_split`, `r2_no_wrap`). This is the carry-propagated
    widening multiply that #474 was blocked on. -/
theorem montmul_fragment_correct (a0 a1 b : BitVec 64) :
    (r0 a0 b).toNat
        + (r1 a0 a1 b).toNat * 2 ^ 64
        + (r2 a0 a1 b).toNat * 2 ^ 128
      = (a0.toNat + a1.toNat * 2 ^ 64) * b.toNat := by
  -- The four established facts, with `lo0/lo1/hi0/hi1` already unfolded to the
  -- underlying products so every atom is shared.
  have e0 : (a0 * b).toNat + (mulHiW a0 b).toNat * 2 ^ 64 = a0.toNat * b.toNat :=
    mulx_reconstruct a0 b
  have e1 : (a1 * b).toNat + (mulHiW a1 b).toNat * 2 ^ 64 = a1.toNat * b.toNat :=
    mulx_reconstruct a1 b
  have ec : (r1 a0 a1 b).toNat + (c1 a0 a1 b).toNat * 2 ^ 64
      = (a1 * b).toNat + (mulHiW a0 b).toNat := by
    have := r1_carry_split a0 a1 b; simpa [lo1, hi0] using this
  have er2 : (r2 a0 a1 b).toNat = (mulHiW a1 b).toNat + (c1 a0 a1 b).toNat := by
    have := r2_no_wrap a0 a1 b; simpa [hi1] using this
  have e128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add]
  -- Rewrite the goal: r0 = lo0, r2 = hi1 + c1, 2^128 = K*K.
  simp only [r0, lo0, e128, er2]
  -- Abstract 2^64 = K and the six product atoms; everything below is core `Nat`
  -- algebra (this VIR subtree is Mathlib-free, so no ring/nlinarith).
  generalize hK : (2 : Nat) ^ 64 = K at e0 e1 ec ⊢
  generalize hlo0 : (a0 * b).toNat = lo0v at e0 ⊢
  generalize hlo1 : (a1 * b).toNat = lo1v at e1 ec
  generalize hhi0 : (mulHiW a0 b).toNat = hi0v at e0 ec
  generalize hhi1 : (mulHiW a1 b).toNat = hi1v at e1 ⊢
  generalize hr1 : (r1 a0 a1 b).toNat = r1v at ec ⊢
  generalize hc1 : (c1 a0 a1 b).toNat = c1v at ec ⊢
  generalize ha0 : a0.toNat = a0n at e0 ⊢
  generalize ha1 : a1.toNat = a1n at e1 ⊢
  generalize hbn : b.toNat = bn at e0 e1 ⊢
  -- e0 : lo0v + hi0v*K = a0n*bn
  -- e1 : lo1v + hi1v*K = a1n*bn
  -- ec : r1v + c1v*K   = lo1v + hi0v
  -- goal: lo0v + r1v*K + (hi1v + c1v)*(K*K) = (a0n + a1n*K)*bn
  -- Scale ec by K (the limb-1 carry crossing into limb 2):
  have ecK : (r1v + c1v * K) * K = (lo1v + hi0v) * K := by rw [ec]
  -- Bridge the nonlinear atoms so omega sees a shared linear set.
  have b1 : (hi1v + c1v) * (K * K) = hi1v * (K * K) + c1v * (K * K) := by
    rw [Nat.add_mul]
  have b2 : (r1v + c1v * K) * K = r1v * K + c1v * K * K := by
    rw [Nat.add_mul, Nat.mul_assoc]
  have b3 : (lo1v + hi0v) * K = lo1v * K + hi0v * K := by rw [Nat.add_mul]
  have b4 : (a0n + a1n * K) * bn = a0n * bn + a1n * K * bn := by rw [Nat.add_mul]
  -- a1n*K*bn = (a1n*bn)*K = (lo1v + hi1v*K)*K  [by e1]
  have b5 : a1n * K * bn = (lo1v + hi1v * K) * K := by
    rw [e1, Nat.mul_right_comm a1n K bn]
  have b6 : (lo1v + hi1v * K) * K = lo1v * K + hi1v * (K * K) := by
    rw [Nat.add_mul, Nat.mul_assoc]
  -- c1v*K*K and c1v*(K*K) are the same atom.
  have b7 : c1v * K * K = c1v * (K * K) := Nat.mul_assoc _ _ _
  rw [b1]
  -- now: lo0v + r1v*K + (hi1v*(K*K) + c1v*(K*K)) = (a0n + a1n*K)*bn
  rw [b4, ← e0, b5, b6]
  -- goal: lo0v + r1v*K + (hi1v*(K*K)+c1v*(K*K)) = lo0v + hi0v*K + (lo1v*K + hi1v*(K*K))
  -- cancel; remaining: r1v*K + c1v*(K*K) = hi0v*K + lo1v*K, which is ec scaled.
  have key : r1v * K + c1v * (K * K) = hi0v * K + lo1v * K := by
    have := ecK; rw [b2, b3, b7] at this; omega
  omega

/-! ## 6. GMP KAT (no fabricated vectors)

Reference limbs for the fixed inputs below were produced by `libgmp`
(`/tmp/montref.c`, the mpn-level reference) and cross-checked with `bc`:

```
a0 = 18364758544493064720   (0xFEDCBA9876543210)
a1 = 81985529216486895      (0x0123456789ABCDEF)
b  = 16045690984503098046   (0xDEADBEEFCAFEBABE)
=> r0 = 11717160183380363232
   r1 = 6658269708175841281
   r2 = 71314182153347102
```

We evaluate the three `Com`s on these inputs and check `Com.denote` matches the
GMP limbs bit-for-bit (`native_decide`: one cheap 3-limb vector, per the
project's "no heavy in-kernel native_decide KAT" guidance). -/

/-- GMP input `a0`. -/ def katA0 : BitVec 64 := 18364758544493064720
/-- GMP input `a1`. -/ def katA1 : BitVec 64 := 81985529216486895
/-- GMP input `b`.  -/ def katB  : BitVec 64 := 16045690984503098046

/-- KAT: the three `Com`s, on the GMP inputs, denote exactly the GMP limbs. -/
theorem montmul_fragment_kat :
    (comR0.denote (val katA0 katA1 katB)).toNat = 11717160183380363232 ∧
    (comR1.denote (val katA0 katA1 katB)).toNat = 6658269708175841281 ∧
    (comR2.denote (val katA0 katA1 katB)).toNat = 71314182153347102 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## 7. Lowering reaches the jasmin MULX / ADCX mnemonics

The export lowers the carry/widening ops to the `MULXHI` / `ADCX` / `ADCXHI`
mnemonics `read_linear.ml` materialises as the BMI2/ADX `sopn`s. We check the
exported `r2` body actually carries those mnemonics — i.e. the dialect's new ops
survive the `Com → Lprog` lowering (not just the denotation). -/

/-- Does any body instruction's `Lopn` carry mnemonic exactly `m`? -/
def bodyHasOpn (m : String) (f : Lfundef) : Bool :=
  f.lfd_body.any (fun i => match i.li_i with
    | .Lopn _ opn _ => opn == m
    | _ => false)

/-- The virtual lprog body of `comR2` contains a `MULXHI:64`, an `ADCXHI:64`
    (the carry-out), and an `ADCX:64` (the carry data word) — the lowered
    images of `mulhi` / `addCarryHi` / `addCarryLo`. These are exactly the
    mnemonics `read_linear.ml` materialises as the BMI2/ADX `sopn`s. -/
theorem comR2_lowers_to_adx :
    ((Com.toLprog comR2 "montmul2x1").lp_funcs.head?.map
        (fun p => bodyHasOpn "MULXHI:64" p.2)) = some true ∧
    ((Com.toLprog comR2 "montmul2x1").lp_funcs.head?.map
        (fun p => bodyHasOpn "ADCXHI:64" p.2)) = some true ∧
    ((Com.toLprog comR2 "montmul2x1").lp_funcs.head?.map
        (fun p => bodyHasOpn "ADCX:64" p.2)) = some true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.MontMulFragmentDemo
