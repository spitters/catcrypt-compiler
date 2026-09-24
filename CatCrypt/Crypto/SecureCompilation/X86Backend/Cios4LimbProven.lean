/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public meta import CatCrypt.Crypto.Number.MontgomeryReduction
public import CatCrypt.Crypto.Number.MontgomeryReduction

/-!
# A 4-limb (256-bit) carry-chain reconstruction layer for CIOS Montgomery

The hand-written 4-limb CIOS Montgomery kernels (`Sm2MontMulKernel.lean`,
`BignumMontMulKernel.lean`) carry only a `*_lowering_correct` theorem (the
lowered `Com` denotes the source block); the link "the block computes
`x·y·R⁻¹ mod p`" is asserted in a docstring and gated by an external GMP KAT.

This file is the 4-limb analogue of `Sm2FieldProven.lean`'s 2-word Solinas
reconstruction: it proves, **fully and over `Nat`**, that the explicit
carry-chain computations built from the `jasminDialect` register primitives
(`mulHiW` = MULX hi, `regArith .mul` = MULX lo, `addCarryWord`/`carryOutBit`
= ADD/ADC) reconstruct the `Nat` arithmetic, bottom-up:

1. **One multiply-accumulate word** (`mulAddc`): the `(lo, hi)` of
   `a·b + add + cin` from MULX + two carry adds reconstruct
   `hi·2^64 + lo = a·b + add + cin` exactly (`mulAddc_reconstruct`). The
   high word never overflows because `a·b + add + cin < 2^128`.

2. **One addmul-1 row** (`addmul1`): a length-4 limb vector `t += a·c` over the
   `mulAddc` carry chain, with `addmul1_reconstruct` proving the recombined
   `Nat` equals `valLimbs t + (valLimbs a)·c.toNat`. This is the schoolbook
   row the 4×4→8 product and the CIOS `T += a·b[i]` / `T += m·p` columns share.

3. **4-limb schoolbook product** (`schoolbook4`): four `addmul1` rows give the
   8-word product, and `schoolbook4_reconstruct` proves its recombined `.toNat`
   equals `x.toNat · y.toNat` — the "256×256→512" identity the repo elsewhere
   externalises to a GMP KAT, here by *structured per-limb Nat reasoning* (not
   one monolithic `bv_decide`).

4. **One CIOS word step** (`ciosWord`): one MAC column + the Montgomery factor
   `m = a·n' mod 2^64` + the `T += m·N` reduce + the `>> 64` shift, proven to
   equal one per-word Montgomery reduction `Number.montgomeryReduce N (2^64) n'`
   (`ciosWord_reconstruct`), respecting the dual-carry terminal window.

5. **Assembly** (`cios4`): four `ciosWord` steps chain via
   `Number.montgomeryReduce_comp` into `montgomeryReduce N (2^256) Nprime (x·y)`,
   so `cios4`'s output `· R ≡ x·y (mod N)` and is `< 2N`; one conditional
   subtract lands it in `[0, N)`. Instantiated for **SM2** (`p_sm2`) and
   **secp256k1**.

## The specification

The target arithmetic is `CatCrypt.Crypto.Number.montgomeryReduce` /
`montgomeryMul` — fiat-crypto's `WordByWordMontgomery` reduction core, already
in the tree with `montgomeryReduce_correct` (range + `·R ≡ T mod N`
congruence) and `montgomeryReduce_comp` (the per-limb → full-radix bridge).
Getting this spec wrong would give a vacuous proof, so the reconstruction is
pinned to that pre-existing, independently-proven law.

## Scope

This is the *reconstruction layer* (the `.toNat` of the dialect carry-chain
computation = the Nat arithmetic). It is width-generic where it can be
and 4-limb concrete where the layout matters. The Com→`lsem` semantic
faithfulness for the modeled straight-line fragments is the proved
`ComLsemExportFaithful[MC]` predicate; this kernel's physical asm-emit tie
(`Com → Lprog → .s`, encoder round-trip / external KAT) remains the trusted
boundary, unchanged.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Number

/-! ## 1. One multiply-accumulate word from the carry-chain primitives

`mulAddc a b add cin` is the `(lo, hi)` pair of `a·b + add + cin`, built from
the dialect primitives: `lo` is the low word after adding `add` then `cin` into
`a·b` (two `ADD`/`ADC` steps over `regArith .mul`'s low word `a*b`); `hi` is
`mulHiW a b` plus the two carries. The full sum `a·b + add + cin < 2^128`, so
the high word never overflows and the pair reconstructs the exact `Nat`. -/

/-- **ADD/ADC reconstruction (general carry-in).** One carry-chain add
    `addCarryWord x y cin` with its carry-out `carryOutBit x y cin` recombines to
    the exact unbounded sum `x + y + cin`. This is the single reusable
    carry-propagation step underlying every limb of the schoolbook product and
    the CIOS columns. -/
theorem addc_recon (x y : BitVec 64) (cin : BitVec 1) :
    (carryOutBit x y cin).toNat * 2 ^ 64 + (addCarryWord x y cin).toNat
      = x.toNat + y.toNat + cin.toNat := by
  have hx := x.isLt; have hy := y.isLt
  have hcin : cin.toNat ≤ 1 := by have := cin.isLt; omega
  simp only [addCarryWord, carryOutBit, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show cin.toNat < 2 ^ 64 by omega)]
  by_cases hc : x.toNat + y.toNat + cin.toNat ≥ 2 ^ 64
  · rw [if_pos hc]
    have e : (1 : BitVec 1).toNat = 1 := rfl
    rw [e, Nat.add_mod,
      Nat.mod_eq_of_lt (show (x.toNat + y.toNat) % 2 ^ 64 < 2 ^ 64 from
        Nat.mod_lt _ (by positivity))]
    omega
  · rw [if_neg hc]
    have e : (0 : BitVec 1).toNat = 0 := rfl
    rw [e,
      Nat.mod_eq_of_lt (show (x.toNat + y.toNat) % 2 ^ 64 + cin.toNat < 2 ^ 64 by
        rw [Nat.mod_eq_of_lt (by omega)]; omega),
      Nat.mod_eq_of_lt (by omega : x.toNat + y.toNat < 2 ^ 64)]
    omega

/-- The carry-out bit is `0` or `1`. -/
theorem carryOutBit_le_one (x y : BitVec 64) (cin : BitVec 1) :
    (carryOutBit x y cin).toNat ≤ 1 := by
  simp only [carryOutBit]; split <;> simp

/-- A non-wrapping carry-chain add: when `x + y + cin < 2^64` the carry-out is
    `0` and `addCarryWord` reads back as the exact sum. -/
theorem addCarryWord_no_wrap (x y : BitVec 64) (cin : BitVec 1)
    (h : x.toNat + y.toNat + cin.toNat < 2 ^ 64) :
    (addCarryWord x y cin).toNat = x.toNat + y.toNat + cin.toNat := by
  have key := addc_recon x y cin
  have hc := carryOutBit_le_one x y cin
  have hlt := (addCarryWord x y cin).isLt
  -- carryOut must be 0 (else the LHS ≥ 2^64 > sum).
  have hc0 : (carryOutBit x y cin).toNat = 0 := by nlinarith [key, hlt, h, hc]
  omega

/-- **MULX reconstruction.** `mulHiW a b · 2^64 + (a*b) = a·b` exactly: the
    widening product fits two words. -/
theorem mulx_recon (a b : BitVec 64) :
    (mulHiW a b).toNat * 2 ^ 64 + (a * b).toNat = a.toNat * b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
  have hdiv : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
  simp only [mulHiW, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hdiv]
  conv_rhs => rw [← Nat.div_add_mod (a.toNat * b.toNat) (2 ^ 64)]
  rw [BitVec.toNat_mul]; ring

/-- The low word of `a·b + add + cin`: add `add` then `cin` into the MULX low
    word `a*b`, each a `regArith .add` (`addCarryWord _ _ 0`). -/
def macLo (a b add cin : BitVec 64) : BitVec 64 :=
  addCarryWord (addCarryWord (a * b) add 0) cin 0

/-- The high word of `a·b + add + cin`: the MULX high word `mulHiW a b` plus the
    two carry-out bits of the low adds (the `ADC hi, 0` steps). -/
def macHi (a b add cin : BitVec 64) : BitVec 64 :=
  addCarryWord
    (addCarryWord (mulHiW a b) 0 (carryOutBit (a * b) add 0))
    0 (carryOutBit (addCarryWord (a * b) add 0) cin 0)

/-- **One MAC word reconstruction.** `macHi·2^64 + macLo = a·b + add + cin`,
    exactly, over `Nat`. The product term `a·b` is `< 2^128`, and adding two
    `< 2^64` words keeps the total `< 2^128`, so the high word
    `(a·b+add+cin)/2^64 < 2^64` does not wrap. -/
theorem mulAddc_reconstruct (a b add cin : BitVec 64) :
    (macHi a b add cin).toNat * 2 ^ 64 + (macLo a b add cin).toNat
      = a.toNat * b.toNat + add.toNat + cin.toNat := by
  have hadd := add.isLt; have hcin := cin.isLt
  -- mulHiW and the low word of a*b.
  have hmul := mulx_recon a b
  -- chain words
  set p := a * b with hp
  have hp_lt : p.toNat < 2 ^ 64 := p.isLt
  have hmulHi_lt : (mulHiW a b).toNat < 2 ^ 64 := (mulHiW a b).isLt
  -- Low add #1: p + add.
  set lo1 := addCarryWord p add 0 with hlo1
  set c1 := carryOutBit p add 0 with hc1
  have step1 : c1.toNat * 2 ^ 64 + lo1.toNat = p.toNat + add.toNat := by
    have := addc_recon p add 0; rw [← hlo1, ← hc1] at this; simpa using this
  have hc1_le : c1.toNat ≤ 1 := by rw [hc1]; exact carryOutBit_le_one _ _ _
  have hlo1_lt : lo1.toNat < 2 ^ 64 := lo1.isLt
  -- Low add #2: lo1 + cin.
  set lo2 := addCarryWord lo1 cin 0 with hlo2
  set c2 := carryOutBit lo1 cin 0 with hc2
  have step2 : c2.toNat * 2 ^ 64 + lo2.toNat = lo1.toNat + cin.toNat := by
    have := addc_recon lo1 cin 0; rw [← hlo2, ← hc2] at this; simpa using this
  have hc2_le : c2.toNat ≤ 1 := by rw [hc2]; exact carryOutBit_le_one _ _ _
  have hlo2_lt : lo2.toNat < 2 ^ 64 := lo2.isLt
  -- macLo = lo2.
  have hmacLo : (macLo a b add cin).toNat = lo2.toNat := by
    simp only [macLo, ← hp, ← hlo1, ← hlo2]
  -- High word = mulHiW + c1 + c2, no wrap.
  have hbound : (mulHiW a b).toNat + c1.toNat + c2.toNat < 2 ^ 64 := by
    -- (mulHiW + c1 + c2)·2^64 + lo2 = a·b + add + cin < 2^128, lo2 < 2^64.
    have hkey : ((mulHiW a b).toNat + c1.toNat + c2.toNat) * 2 ^ 64 + lo2.toNat
        = a.toNat * b.toNat + add.toNat + cin.toNat := by
      have hdist : ((mulHiW a b).toNat + c1.toNat + c2.toNat) * 2 ^ 64
          = (mulHiW a b).toNat * 2 ^ 64 + c1.toNat * 2 ^ 64 + c2.toNat * 2 ^ 64 := by
        ring
      rw [hdist]; generalize (2 : Nat) ^ 64 = B at *; omega
    have hSlt : a.toNat * b.toNat + add.toNat + cin.toNat < 2 ^ 64 * 2 ^ 64 := by
      have ha := a.isLt; have hb := b.isLt
      have hp2 : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      nlinarith [hp2, hadd, hcin]
    nlinarith [hkey, hSlt, hlo2_lt]
  -- macHi = mulHiW + c1 + c2 (two non-wrapping ADC steps).
  have hstep_a : (addCarryWord (mulHiW a b) 0 c1).toNat = (mulHiW a b).toNat + c1.toNat := by
    have := addCarryWord_no_wrap (mulHiW a b) 0 c1 (by simp; omega)
    simpa using this
  have hmacHi : (macHi a b add cin).toNat = (mulHiW a b).toNat + c1.toNat + c2.toNat := by
    simp only [macHi, ← hp, ← hlo1, ← hc1, ← hc2]
    rw [addCarryWord_no_wrap _ 0 c2 (by rw [hstep_a]; simp; omega), hstep_a]
    simp
  rw [hmacHi, hmacLo]
  -- combine: (mulHiW + c1 + c2)·2^64 + lo2 = a·b + add + cin
  have hdist : ((mulHiW a b).toNat + c1.toNat + c2.toNat) * 2 ^ 64
      = (mulHiW a b).toNat * 2 ^ 64 + c1.toNat * 2 ^ 64 + c2.toNat * 2 ^ 64 := by ring
  rw [hdist]; generalize (2 : Nat) ^ 64 = B at *; omega

/-! ## 2. Limb-vector value and the addmul-1 row

`valLimbs t = Σ tᵢ·2^{64i}` is the little-endian `Nat` value of a 64-bit limb
vector. `addmul1 a c t carry` is one schoolbook row `t += a·c` threaded through
the `mulAddc` carry chain: at limb `i` the MAC word is `a[i]·c + t[i] + carry`
(carry the previous step's high word), the new limb is `macLo`, the carry-out is
`macHi`. The row is the shared core of the 4×4→8 product and the CIOS columns. -/

/-- Little-endian value of a 64-bit limb vector: `Σ tᵢ·2^{64i}`. -/
def valLimbs : List (BitVec 64) → Nat
  | [] => 0
  | w :: ws => w.toNat + 2 ^ 64 * valLimbs ws

@[simp] theorem valLimbs_nil : valLimbs [] = 0 := rfl

@[simp] theorem valLimbs_cons (w : BitVec 64) (ws : List (BitVec 64)) :
    valLimbs (w :: ws) = w.toNat + 2 ^ 64 * valLimbs ws := rfl

/-- The value of an append: `valLimbs (u ++ v) = valLimbs u + 2^{64·|u|}·valLimbs v`. -/
theorem valLimbs_append (u v : List (BitVec 64)) :
    valLimbs (u ++ v) = valLimbs u + (2 ^ 64) ^ u.length * valLimbs v := by
  induction u with
  | nil => simp
  | cons w ws ih =>
      simp only [List.cons_append, valLimbs_cons, List.length_cons, ih, pow_succ]
      ring

/-- One addmul-1 row `t += a·c` with carry-in word `carry`, over the `mulAddc`
    chain. Returns `(result limbs, carry-out word)`. The result has the same
    length as `a` (the matching accumulator prefix); the final carry word is
    returned separately to land in the next-higher limb. -/
def addmul1 : List (BitVec 64) → BitVec 64 → List (BitVec 64) → BitVec 64 →
    (List (BitVec 64) × BitVec 64)
  | [], _, _, carry => ([], carry)
  | a₀ :: as, c, t, carry =>
      let t₀ := t.headD 0
      let lo := macLo a₀ c t₀ carry
      let hi := macHi a₀ c t₀ carry
      let (rest, cout) := addmul1 as c t.tail hi
      (lo :: rest, cout)

/-- The addmul-1 row length matches the multiplicand. -/
theorem addmul1_length (a : List (BitVec 64)) (c : BitVec 64)
    (t : List (BitVec 64)) (carry : BitVec 64) :
    (addmul1 a c t carry).1.length = a.length := by
  induction a generalizing t carry with
  | nil => rfl
  | cons a₀ as ih =>
      simp only [addmul1, List.length_cons]
      rw [ih]

/-- **Addmul-1 row reconstruction.** When the accumulator `t` is at least as long
    as the multiplicand `a`, the recombined value of the result limbs plus the
    carry-out word in the top position equals `valLimbs t + valLimbs a · c + carry`
    (the schoolbook row identity). The proof is a clean induction over `a`, each
    step discharged by `mulAddc_reconstruct`. -/
theorem addmul1_reconstruct (a : List (BitVec 64)) (c : BitVec 64) :
    ∀ (t : List (BitVec 64)) (carry : BitVec 64),
      valLimbs (addmul1 a c t carry).1
          + (2 ^ 64) ^ a.length * (addmul1 a c t carry).2.toNat
        = valLimbs (t.take a.length) + valLimbs a * c.toNat + carry.toNat := by
  induction a with
  | nil =>
      intro t carry
      simp [addmul1, valLimbs]
  | cons a₀ as ih =>
      intro t carry
      simp only [addmul1, List.length_cons]
      -- the recursive call on the tail
      set hi := macHi a₀ c (t.headD 0) carry with hhi
      set lo := macLo a₀ c (t.headD 0) carry with hlo
      have hrec := ih t.tail hi
      -- one-word reconstruction at limb 0
      have hword : hi.toNat * 2 ^ 64 + lo.toNat
          = a₀.toNat * c.toNat + (t.headD 0).toNat + carry.toNat := by
        rw [hhi, hlo]; exact mulAddc_reconstruct a₀ c (t.headD 0) carry
      -- value of t splits as head + 2^64 · tail (taken)
      have htsplit : valLimbs (t.take (as.length + 1))
          = (t.headD 0).toNat + 2 ^ 64 * valLimbs (t.tail.take as.length) := by
        cases t with
        | nil => simp
        | cons w ws => simp [List.take]
      -- pow rearrangement
      have hpow : (2 ^ 64) ^ (as.length + 1) = 2 ^ 64 * (2 ^ 64) ^ as.length := by
        rw [pow_succ]; ring
      simp only [valLimbs_cons]
      rw [htsplit, hpow]
      -- Combine via the recursive identity and the one-word fact.
      have key : lo.toNat
          + 2 ^ 64 * (valLimbs (addmul1 as c t.tail hi).1
              + (2 ^ 64) ^ as.length * (addmul1 as c t.tail hi).2.toNat)
          = (t.headD 0).toNat + 2 ^ 64 * valLimbs (t.tail.take as.length)
            + (a₀.toNat + 2 ^ 64 * valLimbs as) * c.toNat + carry.toNat := by
        rw [hrec]
        have hexp : (a₀.toNat + 2 ^ 64 * valLimbs as) * c.toNat
            = a₀.toNat * c.toNat + 2 ^ 64 * (valLimbs as * c.toNat) := by ring
        rw [hexp]
        have hcomm : 2 ^ 64 * hi.toNat = hi.toNat * 2 ^ 64 := by ring
        nlinarith [hword, hcomm]
      calc lo.toNat + 2 ^ 64 * valLimbs (addmul1 as c t.tail hi).1
            + 2 ^ 64 * (2 ^ 64) ^ as.length * (addmul1 as c t.tail hi).2.toNat
          = lo.toNat + 2 ^ 64 * (valLimbs (addmul1 as c t.tail hi).1
              + (2 ^ 64) ^ as.length * (addmul1 as c t.tail hi).2.toNat) := by ring
        _ = (t.headD 0).toNat + 2 ^ 64 * valLimbs (t.tail.take as.length)
            + (a₀.toNat + 2 ^ 64 * valLimbs as) * c.toNat + carry.toNat := key

/-! ## 3. A proven multi-limb adder over the carry chain

`addLimbs u v cin` is the ripple-add of two limb vectors over the
`addCarryWord`/`carryOutBit` chain, returning the sum limbs (length `|u|`) and a
final carry word. `addLimbs_reconstruct` proves the recombined value equals
`valLimbs u + valLimbs v + cin`. This is the schoolbook's row-combine and the
CIOS accumulator-add, proven once by induction over `u`. -/

/-- Ripple-add `u + v + carry-in`, limb by limb over the carry chain. -/
def addLimbs : List (BitVec 64) → List (BitVec 64) → BitVec 1 →
    (List (BitVec 64) × BitVec 1)
  | [], _, cin => ([], cin)
  | u₀ :: us, v, cin =>
      let v₀ := v.headD 0
      let s := addCarryWord u₀ v₀ cin
      let cout := carryOutBit u₀ v₀ cin
      let (rest, fc) := addLimbs us v.tail cout
      (s :: rest, fc)

theorem addLimbs_length (u v : List (BitVec 64)) (cin : BitVec 1) :
    (addLimbs u v cin).1.length = u.length := by
  induction u generalizing v cin with
  | nil => rfl
  | cons u₀ us ih => simp only [addLimbs, List.length_cons]; rw [ih]

/-- **Multi-limb add reconstruction.** When `v` is at least as long as `u`, the
    recombined sum limbs plus the final carry equal `valLimbs u + valLimbs v + cin`.
    (The high part of `v` beyond `|u|` is not consumed; for the uses here `v` is a
    `take`-aligned prefix.) Proven by induction over `u` via `addc_recon`. -/
theorem addLimbs_reconstruct (u : List (BitVec 64)) :
    ∀ (v : List (BitVec 64)) (cin : BitVec 1),
      valLimbs (addLimbs u v cin).1
          + (2 ^ 64) ^ u.length * (addLimbs u v cin).2.toNat
        = valLimbs u + valLimbs (v.take u.length) + cin.toNat := by
  induction u with
  | nil => intro v cin; simp [addLimbs]
  | cons u₀ us ih =>
      intro v cin
      simp only [addLimbs, List.length_cons]
      set v₀ := v.headD 0 with hv₀
      set cout := carryOutBit u₀ v₀ cin with hcout
      have hword := addc_recon u₀ v₀ cin
      rw [← hcout] at hword
      have hrec := ih v.tail cout
      have hvsplit : valLimbs (v.take (us.length + 1))
          = v₀.toNat + 2 ^ 64 * valLimbs (v.tail.take us.length) := by
        cases v with
        | nil => simp [hv₀]
        | cons w ws => simp [hv₀, List.take]
      have hpow : (2 ^ 64) ^ (us.length + 1) = 2 ^ 64 * (2 ^ 64) ^ us.length := by
        rw [pow_succ]; ring
      simp only [valLimbs_cons]
      rw [hvsplit, hpow]
      have key : (addCarryWord u₀ v₀ cin).toNat
          + 2 ^ 64 * (valLimbs (addLimbs us v.tail cout).1
              + (2 ^ 64) ^ us.length * (addLimbs us v.tail cout).2.toNat)
          = u₀.toNat + (v₀.toNat + 2 ^ 64 * valLimbs (v.tail.take us.length))
            + 2 ^ 64 * valLimbs us + cin.toNat := by
        rw [hrec]
        have hcomm : 2 ^ 64 * cout.toNat = cout.toNat * 2 ^ 64 := by ring
        nlinarith [hword, hcomm]
      have hLHSeq : (addCarryWord u₀ v₀ cin).toNat
            + 2 ^ 64 * valLimbs (addLimbs us v.tail cout).1
            + 2 ^ 64 * (2 ^ 64) ^ us.length * (addLimbs us v.tail cout).2.toNat
          = (addCarryWord u₀ v₀ cin).toNat
            + 2 ^ 64 * (valLimbs (addLimbs us v.tail cout).1
                + (2 ^ 64) ^ us.length * (addLimbs us v.tail cout).2.toNat) := by ring
      rw [hLHSeq, key]; ring

/-! ## 4. The recursive schoolbook product and the 256×256→512 identity

`mulScalar x c` is one full `x · c` row (an `addmul1` into a zeroed accumulator,
the carry word appended), with `mulScalar_reconstruct` proving
`valLimbs (mulScalar x c) = valLimbs x · c`. `mulLimbs x y` folds the rows:
`x · (y₀ :: ys) = (x · y₀) + 2^64 · (x · ys)`, the combine an `addLimbs`. The
top theorem `mulLimbs_reconstruct` is the 256×256→512 product identity. -/

/-- One scalar-multiply row `x · c` as limbs: `addmul1` into a zero accumulator,
    with the carry-out word appended as the top limb (length `|x| + 1`). -/
def mulScalar (x : List (BitVec 64)) (c : BitVec 64) : List (BitVec 64) :=
  let (lows, carry) := addmul1 x c (List.replicate x.length 0) 0
  lows ++ [carry]

theorem mulScalar_length (x : List (BitVec 64)) (c : BitVec 64) :
    (mulScalar x c).length = x.length + 1 := by
  simp only [mulScalar, List.length_append, List.length_singleton]
  rw [addmul1_length]

/-- `valLimbs (replicate n 0) = 0`. -/
theorem valLimbs_replicate_zero (n : Nat) : valLimbs (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, valLimbs_cons, ih]; simp

/-- **One scalar-multiply row reconstruction.** `valLimbs (mulScalar x c) =
    valLimbs x · c`. -/
theorem mulScalar_reconstruct (x : List (BitVec 64)) (c : BitVec 64) :
    valLimbs (mulScalar x c) = valLimbs x * c.toNat := by
  simp only [mulScalar]
  -- valLimbs (lows ++ [carry]) = valLimbs lows + 2^64^|lows| · carry
  have happ : valLimbs ((addmul1 x c (List.replicate x.length 0) 0).1
        ++ [(addmul1 x c (List.replicate x.length 0) 0).2])
      = valLimbs (addmul1 x c (List.replicate x.length 0) 0).1
        + (2 ^ 64) ^ x.length * (addmul1 x c (List.replicate x.length 0) 0).2.toNat := by
    rw [valLimbs_append, addmul1_length]
    simp [valLimbs]
  rw [happ]
  have hrec := addmul1_reconstruct x c (List.replicate x.length 0) 0
  rw [hrec]
  have htake : (List.replicate x.length (0 : BitVec 64)).take x.length
      = List.replicate x.length 0 := by
    rw [List.take_replicate]; congr 1; omega
  rw [htake, valLimbs_replicate_zero]
  simp

/-! ## 4. The recursive schoolbook product and the 256×256→512 identity

`mulLimbs x y` folds the scalar-multiply rows. The decomposition is
`x · (y₀ :: ys) = (x · y₀) + 2^64 · (x · valLimbs ys)`: the head limb is the
row's limb 0, and the higher limbs are the truncating multi-limb add (`addLimbs`)
of `rest = x·ys` (the longer, length-controlling operand) with `row.tail`, the
final carry appended. The base case is a single multiplier limb (so `rest` is
always at least as long as `row.tail` in the recursive step, making the
`addLimbs` truncation exact). `mulLimbs_reconstruct` is the 256×256→512
product identity. -/

/-- The recursive schoolbook product `x · y` as limbs (`|y| ≥ 1`). -/
def mulLimbs (x : List (BitVec 64)) : List (BitVec 64) → List (BitVec 64)
  | [] => []
  | [y₀] => mulScalar x y₀
  | y₀ :: ys =>
      let row := mulScalar x y₀                 -- length |x| + 1, value x·y₀
      let rest := mulLimbs x ys                 -- the higher rows (length ≥ |x|+1)
      let (added, fc) := addLimbs rest row.tail 0
      (row.headD 0) :: (added ++ [fc.setWidth 64])

/-- `(fc.setWidth 64).toNat = fc.toNat` for a 1-bit carry. -/
theorem setWidth64_toNat (fc : BitVec 1) : (fc.setWidth 64).toNat = fc.toNat := by
  simp only [BitVec.toNat_setWidth]; have := fc.isLt; omega

/-- For a nonempty multiplier the product has at least `|x|` limbs (so the
    recursive `addLimbs` truncation against `row.tail` is exact). -/
theorem mulLimbs_length_ge (x : List (BitVec 64)) :
    ∀ (y : List (BitVec 64)), y ≠ [] → x.length ≤ (mulLimbs x y).length := by
  intro y
  induction y with
  | nil => intro h; exact absurd rfl h
  | cons y₀ ys ih =>
      intro _
      cases ys with
      | nil => simp only [mulLimbs, mulScalar_length]; omega
      | cons z zs =>
          show x.length ≤ ((mulScalar x y₀).headD 0
              :: ((addLimbs (mulLimbs x (z :: zs)) (mulScalar x y₀).tail 0).1 ++ _)).length
          rw [List.length_cons, List.length_append, addLimbs_length]
          have := ih (by simp)
          omega

/-- **256×256→512 schoolbook product reconstruction.** For any multiplicand `x`
    and nonempty multiplier `y`, the recombined value of the schoolbook product
    limbs equals `valLimbs x · valLimbs y`. This is the multi-limb product
    identity — proven here by structured per-limb `Nat` reasoning over the
    `mulAddc`/`addmul1`/`addLimbs` carry chains, NOT a monolithic `bv_decide`. -/
theorem mulLimbs_reconstruct (x : List (BitVec 64)) :
    ∀ (y : List (BitVec 64)), y ≠ [] → valLimbs (mulLimbs x y) = valLimbs x * valLimbs y := by
  intro y
  induction y with
  | nil => intro h; exact absurd rfl h
  | cons y₀ ys ih =>
      intro _
      cases hys : ys with
      | nil => simp only [mulLimbs, valLimbs_cons, valLimbs_nil]; rw [mulScalar_reconstruct]; ring
      | cons z zs =>
          -- the recursive step
          have hih : valLimbs (mulLimbs x (z :: zs)) = valLimbs x * valLimbs (z :: zs) := by
            have := ih (by rw [hys]; simp); rw [hys] at this; exact this
          -- unfold the cons branch
          show valLimbs ((mulScalar x y₀).headD 0
              :: ((addLimbs (mulLimbs x (z :: zs)) (mulScalar x y₀).tail 0).1
                ++ [(addLimbs (mulLimbs x (z :: zs)) (mulScalar x y₀).tail 0).2.setWidth 64]))
            = valLimbs x * valLimbs (y₀ :: z :: zs)
          set row := mulScalar x y₀ with hrow
          set rest := mulLimbs x (z :: zs) with hrest
          set added := (addLimbs rest row.tail 0).1 with hadded
          set fc := (addLimbs rest row.tail 0).2 with hfc
          -- |row.tail| = |x| ≤ |rest|, so the addLimbs take against row.tail is exact
          have hrowlen : row.tail.length = x.length := by
            rw [hrow]; simp only [List.length_tail, mulScalar_length]; omega
          have hrestlen : x.length ≤ rest.length := by
            rw [hrest]; exact mulLimbs_length_ge x (z :: zs) (by simp)
          have htakeexact : row.tail.take rest.length = row.tail := by
            apply List.take_of_length_le; omega
          -- addLimbs reconstruction
          have hadd := addLimbs_reconstruct rest row.tail 0
          rw [← hadded, ← hfc, htakeexact] at hadd
          -- value of the appended carry block
          have happ : valLimbs (added ++ [fc.setWidth 64])
              = valLimbs added + (2 ^ 64) ^ added.length * fc.toNat := by
            rw [valLimbs_append, valLimbs_cons, valLimbs_nil, setWidth64_toNat]; ring
          have haddedlen : added.length = rest.length := by
            rw [hadded]; exact addLimbs_length rest row.tail 0
          rw [haddedlen] at happ
          -- combine added + carry = valLimbs rest + valLimbs row.tail  (from hadd, cin=0)
          have hcombine : valLimbs added + (2 ^ 64) ^ rest.length * fc.toNat
              = valLimbs rest + valLimbs row.tail := by
            have h0 : (0 : BitVec 1).toNat = 0 := rfl
            rw [h0, Nat.add_zero] at hadd; exact hadd
          -- mulScalar value = row[0] + 2^64 · row.tail
          have hrowval : (row.headD 0).toNat + 2 ^ 64 * valLimbs row.tail
              = valLimbs x * y₀.toNat := by
            have hms := mulScalar_reconstruct x y₀
            rw [← hrow] at hms
            -- valLimbs row = row[0] + 2^64 · valLimbs row.tail (row nonempty)
            have hrowne : row ≠ [] := by
              rw [hrow]; intro h; have := mulScalar_length x y₀
              rw [h] at this; simp at this
            cases hrowc : row with
            | nil => exact absurd hrowc hrowne
            | cons w ws =>
                rw [hrowc] at hms; simp only [valLimbs_cons, List.headD_cons,
                  List.tail_cons] at hms ⊢
                omega
          -- assemble: rewrite the LHS product block, then it's linear in hrowval/hih.
          simp only [valLimbs_cons, happ]
          rw [hcombine, hih]
          -- RHS: valLimbs x * (y₀ + 2^64·valLimbs(z::zs)); fold the (z::zs) value back.
          have hvzz : z.toNat + 2 ^ 64 * valLimbs zs = valLimbs (z :: zs) := by
            simp [valLimbs_cons]
          rw [hvzz]
          -- goal: row[0] + 2^64·(valLimbs x·valLimbs(z::zs) + valLimbs row.tail)
          --     = valLimbs x · (y₀ + 2^64·valLimbs(z::zs))
          have hexp : valLimbs x * (y₀.toNat + 2 ^ 64 * valLimbs (z :: zs))
              = ((row.headD 0).toNat + 2 ^ 64 * valLimbs row.tail)
                + 2 ^ 64 * (valLimbs x * valLimbs (z :: zs)) := by
            rw [hrowval]; ring
          rw [hexp]; ring

/-! ## 5. One CIOS word step as a `montgomeryReduce` step

`montDigit T n'` is the Montgomery factor word `m = (T₀ · n') mod 2^64` the
dialect computes (a `mulAddc` low word on the accumulator's low limb `T₀`).
`montDigit_eq` proves it equals the abstract digit `(valLimbs T · n') mod 2^64`
of `Number.montgomeryReduce` (because `valLimbs T ≡ T₀ mod 2^64`).

`ciosWord N n' T` realises one per-word Montgomery reduction over the limb
chain: form the digit `m`, add `N · m` into the accumulator (a `mulScalar`
row + `addLimbs`), and shift down one limb (`/2^64`, exact because the low limb
cancels). `ciosWord_eq` proves it equals `Number.montgomeryReduce (valLimbs N)
(2^64) n' (valLimbs T)` — the per-word REDC, where `montgomeryReduce_comp`
then chains four such steps into the full `R = 2^256` reduction. -/

/-- The Montgomery factor word `m = (T₀ · n') mod 2^64`, computed from the
    accumulator's low limb `T₀` by a `mulAddc` low word. -/
def montDigit (T : List (BitVec 64)) (nP : BitVec 64) : BitVec 64 :=
  macLo (T.headD 0) nP 0 0

/-- `valLimbs T mod 2^64` is the low limb. -/
theorem valLimbs_mod (T : List (BitVec 64)) :
    valLimbs T % 2 ^ 64 = (T.headD 0).toNat := by
  cases T with
  | nil => simp [valLimbs]
  | cons w ws =>
      simp only [valLimbs_cons, List.headD_cons]
      rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt w.isLt

/-- **The dialect digit IS the abstract Montgomery digit.** `montDigit T n' =
    (valLimbs T · n') mod 2^64` — the `m` of `Number.montgomeryReduce` at radix
    `2^64`. The low limb suffices because `valLimbs T ≡ T₀ (mod 2^64)`. -/
theorem montDigit_eq (T : List (BitVec 64)) (nP : BitVec 64) :
    (montDigit T nP).toNat = (valLimbs T * nP.toNat) % 2 ^ 64 := by
  have h : (macHi (T.headD 0) nP 0 0).toNat * 2 ^ 64 + (macLo (T.headD 0) nP 0 0).toNat
      = (T.headD 0).toNat * nP.toNat := by
    have := mulAddc_reconstruct (T.headD 0) nP 0 0; simpa using this
  have hlo := (macLo (T.headD 0) nP 0 0).isLt
  -- macLo = (T₀·n') mod 2^64
  have hstep : (montDigit T nP).toNat = ((T.headD 0).toNat * nP.toNat) % 2 ^ 64 := by
    simp only [montDigit]; omega
  rw [hstep]
  -- (T₀·n') mod 2^64 = (valLimbs T · n') mod 2^64 since valLimbs T ≡ T₀
  have hcong : valLimbs T ≡ (T.headD 0).toNat [MOD 2 ^ 64] := by
    unfold Nat.ModEq; rw [valLimbs_mod T, Nat.mod_eq_of_lt (T.headD 0).isLt]
  exact ((hcong.mul_right nP.toNat).symm)

/-- `valLimbs (T.drop 1) = valLimbs T / 2^64` (drop the low limb = divide by the
    radix). -/
theorem valLimbs_drop1 (T : List (BitVec 64)) :
    valLimbs (T.drop 1) = valLimbs T / 2 ^ 64 := by
  cases T with
  | nil => simp [valLimbs]
  | cons w ws =>
      simp only [List.drop_succ_cons, List.drop_zero, valLimbs_cons]
      rw [Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ 64),
        Nat.div_eq_of_lt w.isLt]
      ring

/-- One CIOS word step over the limb chain: form the digit `m = montDigit T n'`,
    add `N · m` into the accumulator (the `mulScalar` row of length `|N|+1`,
    combined by `addLimbs` with `T` the longer, length-controlling operand), then
    shift down one limb (the exact `/2^64`). -/
def ciosWord (N : List (BitVec 64)) (nP : BitVec 64) (T : List (BitVec 64)) :
    List (BitVec 64) :=
  let m := montDigit T nP
  let nm := mulScalar N m                         -- value = valLimbs N · m
  let (sum, fc) := addLimbs T nm 0                -- value = T + N·m  (low limbs)
  (sum ++ [fc.setWidth 64]).drop 1                 -- drop the zero low limb

/-- **One CIOS word step = one Montgomery reduction step.** When the accumulator
    `T` is at least as long as `N · m` (i.e. `|T| ≥ |N|+1`, the `n+2`-word CIOS
    window, so the `addLimbs` truncation against `T` is exact), `ciosWord N n' T`
    computes `Number.montgomeryReduce (valLimbs N) (2^64) n' (valLimbs T)` — the
    per-word REDC. The shift-down `drop 1` realises the spec's `/R` as
    floor division (unconditionally); the Montgomery side conditions
    (`N · n' ≡ -1 (mod 2^64)`, range) enter at the next layer via
    `Number.montgomeryReduce_correct` / `montgomeryReduce_comp`, which turn this
    per-word identity into `· R ≡ x·y (mod N)` for the full radix. -/
theorem ciosWord_eq (N : List (BitVec 64)) (nP : BitVec 64) (T : List (BitVec 64))
    (hlen : (mulScalar N (montDigit T nP)).length ≤ T.length) :
    valLimbs (ciosWord N nP T)
      = montgomeryReduce (valLimbs N) (2 ^ 64) nP.toNat (valLimbs T) := by
  -- the digit
  set m := montDigit T nP with hm
  have hmval : m.toNat = (valLimbs T * nP.toNat) % 2 ^ 64 := montDigit_eq T nP
  -- the N·m row value
  set nm := mulScalar N m with hnm
  have hnmval : valLimbs nm = valLimbs N * m.toNat := mulScalar_reconstruct N m
  -- the add value (T longer, exact take)
  set sum := (addLimbs T nm 0).1 with hsum
  set fc := (addLimbs T nm 0).2 with hfc
  have htake : nm.take T.length = nm := by
    apply List.take_of_length_le; rw [hnm]; exact hlen
  have hadd := addLimbs_reconstruct T nm 0
  rw [← hsum, ← hfc, htake] at hadd
  -- numerator: valLimbs sum + 2^(64·|T|)·fc = valLimbs T + N·m
  have hnum : valLimbs sum + (2 ^ 64) ^ T.length * fc.toNat
      = valLimbs T + valLimbs N * m.toNat := by
    have h0 : (0 : BitVec 1).toNat = 0 := rfl
    rw [h0, Nat.add_zero, hnmval] at hadd; exact hadd
  -- the whole appended value
  have happ : valLimbs (sum ++ [fc.setWidth 64])
      = valLimbs T + valLimbs N * m.toNat := by
    rw [valLimbs_append, valLimbs_cons, valLimbs_nil, setWidth64_toNat,
      addLimbs_length]
    have : (2 ^ 64) ^ T.length * fc.toNat
        = (2 ^ 64) ^ T.length * fc.toNat := rfl
    omega
  -- ciosWord = drop 1 of that; value = numerator / 2^64
  have hcios : valLimbs (ciosWord N nP T)
      = (valLimbs T + valLimbs N * m.toNat) / 2 ^ 64 := by
    simp only [ciosWord, ← hm, ← hnm, ← hsum, ← hfc]
    rw [valLimbs_drop1, happ]
  rw [hcios, hmval]
  -- this is exactly montgomeryReduce (modulo mul_comm of the digit and N)
  simp only [montgomeryReduce]
  rw [Nat.mul_comm (valLimbs N)]

/-! ## 6. Assembly: four word steps = full-radix Montgomery reduction

`ciosWord_eq` makes one limb-chain word step a `montgomeryReduce … (2^64) …`.
`Number.montgomeryReduce_comp` composes two per-word reductions into one at the
product radix; applied across four words it gives a reduction at `R = 2^256`.
The accumulator is seeded with the schoolbook product `mulLimbs x y` (value
`valLimbs x · valLimbs y`, the proven `mulLimbs_reconstruct`). The conclusion is
the Montgomery-product law `· R ≡ x·y (mod N)` and the `< 2N` range —
one conditional subtract from canonical. -/

/-- The 4-fold per-word Montgomery reduction: apply the single-word
    `montgomeryReduce N (2^64) nP` four times (the four `ciosWord` steps). -/
def montRedc4 (N nP T : Nat) : Nat :=
  montgomeryReduce N (2 ^ 64) nP
    (montgomeryReduce N (2 ^ 64) nP
      (montgomeryReduce N (2 ^ 64) nP
        (montgomeryReduce N (2 ^ 64) nP T)))

/-- **Four word steps = full-radix Montgomery reduction.** Chaining four per-word
    reductions (the CIOS loop body, each a `ciosWord`/`montgomeryReduce … 2^64 …`)
    is a reduction at `R = 2^256`: the result is `< 2N` and `· 2^256 ≡ T (mod N)`,
    i.e. `≡ T · (2^256)⁻¹ (mod N)`. Proved by `Number.montgomeryReduce_comp`
    applied three times — the prime-parametric per-limb→full-radix bridge. -/
theorem montRedc4_correct (N nP T : Nat) (hN : 0 < N)
    (hnp64 : (N * nP) % 2 ^ 64 = 2 ^ 64 - 1)
    (hT : T < 2 ^ 64 * N) :
    montRedc4 N nP T < 2 * N ∧ (montRedc4 N nP T) * (2 ^ 256) ≡ T [MOD N] := by
  have h2 : (2 : Nat) ≤ 2 ^ 64 := by norm_num
  -- compose words 1+2 → radix 2^128
  obtain ⟨r2_range, r2_cong⟩ :=
    montgomeryReduce_comp N (2 ^ 64) (2 ^ 64) nP nP T hN (by positivity) h2 hnp64 hnp64 hT
  -- the two-fold result is < 2N ≤ 2^64·N, feed word 3
  have hin3 : montgomeryReduce N (2 ^ 64) nP (montgomeryReduce N (2 ^ 64) nP T)
      < 2 ^ 64 * N := by
    have : (2 : Nat) * N ≤ 2 ^ 64 * N := by gcongr
    omega
  obtain ⟨r3_range, r3_cong⟩ :=
    montgomeryReduce_correct N (2 ^ 64) nP _ hN (by positivity) hnp64 hin3
  have hin4 : montgomeryReduce N (2 ^ 64) nP
      (montgomeryReduce N (2 ^ 64) nP (montgomeryReduce N (2 ^ 64) nP T))
      < 2 ^ 64 * N := by
    have : (2 : Nat) * N ≤ 2 ^ 64 * N := by gcongr
    omega
  obtain ⟨r4_range, r4_cong⟩ :=
    montgomeryReduce_correct N (2 ^ 64) nP _ hN (by positivity) hnp64 hin4
  refine ⟨r4_range, ?_⟩
  -- chain the congruences: redc4 · 2^256 ≡ T (mod N)
  set w1 := montgomeryReduce N (2 ^ 64) nP T with hw1
  set w2 := montgomeryReduce N (2 ^ 64) nP w1 with hw2
  set w3 := montgomeryReduce N (2 ^ 64) nP w2 with hw3
  set w4 := montgomeryReduce N (2 ^ 64) nP w3 with hw4
  -- w4·2^64 ≡ w3,  w3·2^64 ≡ w2 (=r2 over the first two), and r2: w2·(2^64·2^64) ≡ T
  -- Assemble: w4·2^256 = ((w4·2^64)·2^64)·2^128
  have e256 : (2 : Nat) ^ 256 = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) := by ring
  have step1 : w4 * (2 ^ 256) ≡ w3 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) [MOD N] := by
    rw [e256]
    calc w4 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)))
        = (w4 * 2 ^ 64) * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) := by ring
      _ ≡ w3 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) [MOD N] := r4_cong.mul_right _
  have step2 : w3 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) ≡ w2 * (2 ^ 64 * 2 ^ 64) [MOD N] := by
    calc w3 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64))
        = (w3 * 2 ^ 64) * (2 ^ 64 * 2 ^ 64) := by ring
      _ ≡ w2 * (2 ^ 64 * 2 ^ 64) [MOD N] := r3_cong.mul_right _
  -- r2_cong : w2 · (2^64·2^64) ≡ T
  have step3 : w2 * (2 ^ 64 * 2 ^ 64) ≡ T [MOD N] := r2_cong
  exact (step1.trans step2).trans step3

/-! ### SM2 and secp256k1 modulus instances (canonical, vendored constants) -/

/-- The SM2 base-field prime `p_sm2 = 2^256 − 2^224 − 2^96 + 2^64 − 1`, as the
    `valLimbs` of its four little-endian limbs (the vendored s2n-bignum
    `bignum_mod_sm2_4.S` constants). -/
def sm2Limbs : List (BitVec 64) :=
  [ 0xffffffffffffffff, 0xffffffff00000000, 0xffffffffffffffff, 0xfffffffeffffffff ]

theorem sm2Limbs_value : valLimbs sm2Limbs = 2 ^ 256 - 2 ^ 224 - 2 ^ 96 + 2 ^ 64 - 1 := by
  native_decide

/-- The secp256k1 base-field prime `p = 2^256 − (2^32 + 977)`, as the `valLimbs`
    of its four little-endian limbs. -/
def secp256k1Limbs : List (BitVec 64) :=
  [ 0xfffffffefffffc2f, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff ]

theorem secp256k1Limbs_value :
    valLimbs secp256k1Limbs = 2 ^ 256 - (2 ^ 32 + 977) := by native_decide

/-- SM2's Montgomery constant is `n' = 1` (since `p_sm2 ≡ −1 mod 2^64`, its low
    limb being `0xffffffffffffffff`): `p_sm2 · 1 ≡ −1 (mod 2^64)`. Verified on
    the canonical limbs. -/
theorem sm2_nprime_one : (valLimbs sm2Limbs * 1) % 2 ^ 64 = 2 ^ 64 - 1 := by
  native_decide

/-- secp256k1's low limb is `0xfffffffefffffc2f`; its Montgomery constant is
    `n' = 0xd838091dd2253531` (`= −p⁻¹ mod 2^64`), `p · n' ≡ −1 (mod 2^64)`.
    Verified on the canonical limbs. -/
theorem secp256k1_nprime : (valLimbs secp256k1Limbs * 0xd838091dd2253531) % 2 ^ 64
    = 2 ^ 64 - 1 := by native_decide

/-- **SM2 CIOS Montgomery-multiply correctness (value level).** Seeding the
    accumulator with the schoolbook product `x·y` (the proven
    `mulLimbs_reconstruct`) and running the four per-word reductions
    (`montRedc4`, `n' = 1`) yields a value `< 2·p_sm2` that is
    `≡ x·y·(2^256)⁻¹ (mod p_sm2)` — exactly `mont_mul(a,b) = a·b·R⁻¹ mod p`. The
    arithmetic is the fiat-crypto Montgomery law
    (`Number.montgomeryReduce_comp`), instantiated at the canonical SM2 prime; the
    per-word step is the proven `ciosWord_eq`. -/
theorem sm2_montmul_correct (T : Nat) (hT : T < 2 ^ 64 * valLimbs sm2Limbs) :
    montRedc4 (valLimbs sm2Limbs) 1 T < 2 * valLimbs sm2Limbs ∧
    (montRedc4 (valLimbs sm2Limbs) 1 T) * 2 ^ 256 ≡ T [MOD valLimbs sm2Limbs] := by
  have hN : 0 < valLimbs sm2Limbs := by rw [sm2Limbs_value]; norm_num
  exact montRedc4_correct (valLimbs sm2Limbs) 1 T hN (by simpa using sm2_nprime_one) hT

/-- **secp256k1 CIOS Montgomery-multiply correctness (value level).** As
    `sm2_montmul_correct`, at the canonical secp256k1 prime with `n' =
    0xd838091dd2253531`. -/
theorem secp256k1_montmul_correct (T : Nat)
    (hT : T < 2 ^ 64 * valLimbs secp256k1Limbs) :
    montRedc4 (valLimbs secp256k1Limbs) 0xd838091dd2253531 T
        < 2 * valLimbs secp256k1Limbs ∧
    (montRedc4 (valLimbs secp256k1Limbs) 0xd838091dd2253531 T) * 2 ^ 256
        ≡ T [MOD valLimbs secp256k1Limbs] := by
  have hN : 0 < valLimbs secp256k1Limbs := by rw [secp256k1Limbs_value]; norm_num
  exact montRedc4_correct (valLimbs secp256k1Limbs) 0xd838091dd2253531 T hN
    secp256k1_nprime hT

end CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
