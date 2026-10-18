/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# `mpn_addmul_1` and `mpn_submul_1` as front-generated runtime-trip loops

`mpn_addmul_1(rp, up, n, v)` sets `rp[0..n) += up[0..n) * v` and `mpn_submul_1`
sets `rp[0..n) -= up[0..n) * v`; both produce a top carry limb. Both kernels are
sourced through the runtime-loop front: the per-limb body is covered `LowCT`
(`RArrLoad` / `RScalarSetExpr` / `RArrStore` over the runtime loop index), and
`Dialects.TranslateDialectRuntimeLoop.rolledForLoopNRt` front-compiles it and
wraps it in a `ComL.forLoopNRt` — one body copy behind a `jne` back-edge, the
trip counter seeded from the runtime `n` register.

## The carry cell

`mpn_mul_1` can let the running carry ride in cell `idx` of the output array,
because that cell is dead on entry to trip `idx`. Here cell `idx` carries the
accumulator limb `rp[idx]`, which the body must read, so the carry needs a cell
of its own. The body takes the limb count `n` as a loop invariant and uses cell
`n` — one past the accumulated words, untouched by every trip — as the carry
cell: trip `idx` reads `rp[n]` as the carry-in and writes the carry-out back to
`rp[n]`. On exit `rp[n]` holds the carry limb, which is the cell a schoolbook
`mpn_mul` assigns from `mpn_addmul_1`'s return value.

## ABI

```c
extern uint64_t *mpn_addmul_1_rt(uint64_t *rp, const uint64_t *up, uint64_t n,
                                 uint64_t v);
extern uint64_t *mpn_submul_1_rt(uint64_t *rp, const uint64_t *up, uint64_t n,
                                 uint64_t v);
```

`rp` (RDI), `up` (RSI), `n` (RDX), `v` (RCX). `rp` holds `n + 1` words, with
`rp[n]` zero on entry and the carry limb on exit.

## Invariant order

The looped ABI export derives each loop invariant's SIB base name from the
invariant's position in the `invs` list: invariant `i` is outer argument
`i + 1`. The invariants are therefore listed `[up, n, v]`, matching
`up = a1`, `n = a2`, `v = a3`; a different order reroutes the `up` load through
another argument's save slot.

## Main results

* `addmulLimb_val` / `submulLimb_val`: the per-limb identities
  `low + 2^64 · carry-out = o + a · b + cy` and
  `low + a · b + cy = o + 2^64 · carry-out`.
* `accFold_val`: the loop invariant over the memref carrier, for a step
  satisfying the signed per-limb identity `LimbAcc σ` — after `n` trips,
  `value (rp'[0..n)) + σ · 2^(64n) · carry-out
     = value (rp[0..n)) + σ · (value (up[0..n)) · b + carry-in)`,
  for every `NR`, `NU` and carry-cell index.
* `addmulFold_val` / `submulFold_val`: that invariant at `σ = 1` and `σ = -1`.
* `addmulFold_val_zero` / `submulFold_val_zero`: the same at carry-in zero, the
  caller's contract.
* `addmulRtProg_denote` / `submulRtProg_denote`: each runtime-trip loop
  program's denotation as the `JLoopBodyN` fold of the front-compiled body.
* `addmulRtAsmOpt` / `submulRtAsmOpt`: the rendered AT&T `.s` text.

## Arithmetic

`addmulLimb` and `submulLimb` are the per-limb word steps. Both carry-out bits
are synthesised branch-free by `FieldReduceIdioms.bSltu`, the shape the covered
`SExpr` fragment admits: `SLt` has no dialect lowering and `srcClean` excludes
it. `accStep` / `accFold` are the same chain over the memref carrier, in the
`(List.range n).foldl` shape `JLoopBodyN.denote` uses; `accFold_val` is the
invariant, proved once for both kernels by carrying the sign `σ : ℤ` of the
accumulation.

## Scope

The arithmetic results hold for every `NR` / `NU` / carry-cell index; `NU` fixes
only the memref width of the concrete front-compiled instances below, whose
rendered SIB accesses are byte-offset and so size-agnostic.

`addmulRtProg_denote` / `submulRtProg_denote` carry the front-compilation
hypothesis `frontLoopBodyJ … = some update` and conclude at `JLoopBodyN.denote`
of that `update`. Identifying that denotation with `accStep` — so that
`accFold_val` reads as a statement about the emitted kernel — is the separate
source-preservation step (`translateDialectControl_denote_ctl` composed with
`cryptoDialectToJasminCom`), not established here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu bSltu_eq)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal bignumVal_snoc)
open CatCrypt.Crypto.SecureCompilation.VIR.MontMulFragmentDemo
  (mulHiW_le mulx_reconstruct)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (cells cells_succ cells_length memGetDyn_memSetDyn_ne memGetDyn_memSetDyn_self
   addCarry_split bSltu_le_one notE orE sv ltuCmds seqAll rpLoc upLoc NU NR
   r64 AR AU Gouter)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-! ## 1. The per-limb word steps -/

/-- The borrow-out bit of `x - y` is `1` exactly when `x <ᵤ y`, and the
    difference is the wrapped word: `(x - y) + y = x + 2^64 · borrow`. -/
theorem subBorrow_split (x y : BitVec 64) :
    (x - y).toNat + y.toNat = x.toNat + 2 ^ 64 * (bSltu x y).toNat := by
  have hx := x.isLt
  have hy := y.isLt
  have hsub : (x - y).toNat = (2 ^ 64 - y.toNat + x.toNat) % 2 ^ 64 := by
    simp [BitVec.toNat_sub]
  rw [bSltu_eq]
  by_cases h : x.toNat < y.toNat
  · have hlt : x.ult y = true := by simp [BitVec.ult, h]
    rw [if_pos hlt, hsub, Nat.mod_eq_of_lt (by omega)]
    simp only [show ((1 : BitVec 64).toNat) = 1 from rfl]
    omega
  · have hlt : x.ult y = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt]
      omega
    rw [if_neg (by simp [hlt]), hsub, Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (by omega)]
    simp only [show ((0 : BitVec 64).toNat) = 0 from rfl]
    omega

/-- One `mpn_addmul_1` limb step on words: multiply limb `a` by the scalar `b`,
    add the running carry `cy` and the accumulator limb `o`, and split into
    `(low word, carry-out)`. Both carry-out bits are the branch-free `bSltu` of
    a sum against its left summand. -/
def addmulLimb (o a b cy : BitVec 64) : BitVec 64 × BitVec 64 :=
  (a * b + cy + o,
    mulHiW a b + bSltu (a * b + cy) (a * b) + bSltu (a * b + cy + o) (a * b + cy))

/-- One `mpn_submul_1` limb step on words: multiply limb `a` by the scalar `b`,
    add the running carry `cy`, and subtract the low word from the accumulator
    limb `o`, splitting into `(low word, carry-out)`. The borrow bit is the
    branch-free `bSltu` of `o` against the subtrahend. -/
def submulLimb (o a b cy : BitVec 64) : BitVec 64 × BitVec 64 :=
  (o - (a * b + cy),
    mulHiW a b + bSltu (a * b + cy) (a * b) + bSltu o (a * b + cy))

/-- **The single-limb multiply-accumulate identity.** `addmulLimb o a b cy`
    splits `o + a * b + cy` into a low word and a carry-out word. -/
theorem addmulLimb_val (o a b cy : BitVec 64) :
    (addmulLimb o a b cy).1.toNat + 2 ^ 64 * (addmulLimb o a b cy).2.toNat
      = o.toNat + (a.toNat * b.toNat + cy.toNat) := by
  have hprod := mulx_reconstruct a b
  have h1 := addCarry_split (a * b) cy
  have h2 := addCarry_split (a * b + cy) o
  have hc1 := bSltu_le_one (a * b + cy) (a * b)
  have hc2 := bSltu_le_one (a * b + cy + o) (a * b + cy)
  have hhi := mulHiW_le a b
  have hble := b.isLt
  have hale := a.isLt
  have hpb : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hnum : (2 ^ 64 - 1) * (2 ^ 64 - 1) = 2 ^ 128 - 2 ^ 65 + 1 := by norm_num
  have hlow : (a * b + cy + o).toNat < 2 ^ 64 := (a * b + cy + o).isLt
  have hcybound : (mulHiW a b).toNat + (bSltu (a * b + cy) (a * b)).toNat
      + (bSltu (a * b + cy + o) (a * b + cy)).toNat < 2 ^ 64 := by
    have ho := o.isLt
    have hcyb := cy.isLt
    omega
  have hsum01 : (mulHiW a b + bSltu (a * b + cy) (a * b)).toNat
      = (mulHiW a b).toNat + (bSltu (a * b + cy) (a * b)).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hsum : (mulHiW a b + bSltu (a * b + cy) (a * b)
        + bSltu (a * b + cy + o) (a * b + cy)).toNat
      = (mulHiW a b).toNat + (bSltu (a * b + cy) (a * b)).toNat
        + (bSltu (a * b + cy + o) (a * b + cy)).toNat := by
    rw [BitVec.toNat_add, hsum01, Nat.mod_eq_of_lt (by omega)]
  simp only [addmulLimb, hsum]
  omega

/-- **The single-limb multiply-subtract identity.** `submulLimb o a b cy`
    splits `o - (a * b + cy)` into a low word and a borrow-carry word:
    `low + a * b + cy = o + 2^64 * carry-out`. -/
theorem submulLimb_val (o a b cy : BitVec 64) :
    (submulLimb o a b cy).1.toNat + (a.toNat * b.toNat + cy.toNat)
      = o.toNat + 2 ^ 64 * (submulLimb o a b cy).2.toNat := by
  have hprod := mulx_reconstruct a b
  have h1 := addCarry_split (a * b) cy
  have h2 := subBorrow_split o (a * b + cy)
  have hc1 := bSltu_le_one (a * b + cy) (a * b)
  have hc2 := bSltu_le_one o (a * b + cy)
  have hhi := mulHiW_le a b
  have hble := b.isLt
  have hale := a.isLt
  have hpb : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hnum : (2 ^ 64 - 1) * (2 ^ 64 - 1) = 2 ^ 128 - 2 ^ 65 + 1 := by norm_num
  have hcybound : (mulHiW a b).toNat + (bSltu (a * b + cy) (a * b)).toNat
      + (bSltu o (a * b + cy)).toNat < 2 ^ 64 := by
    have ho := o.isLt
    have hcyb := cy.isLt
    have hd := (o - (a * b + cy)).isLt
    omega
  have hsum01 : (mulHiW a b + bSltu (a * b + cy) (a * b)).toNat
      = (mulHiW a b).toNat + (bSltu (a * b + cy) (a * b)).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hsum : (mulHiW a b + bSltu (a * b + cy) (a * b)
        + bSltu o (a * b + cy)).toNat
      = (mulHiW a b).toNat + (bSltu (a * b + cy) (a * b)).toNat
        + (bSltu o (a * b + cy)).toNat := by
    rw [BitVec.toNat_add, hsum01, Nat.mod_eq_of_lt (by omega)]
  simp only [submulLimb, hsum]
  omega

/-! ## 2. The carry chain over the memref carrier

The emitted loop carries the whole output array as its accumulator and folds one
body copy over the trip indices. `accStep` is that body's word-level effect and
`accFold` the `(List.range n).foldl` shape `JLoopBodyN.denote` uses. Both are
generic in the per-limb step, so `mpn_addmul_1` and `mpn_submul_1` share the
framing lemmas and the invariant. -/

/-- The signed per-limb accumulation identity a step must satisfy: with `σ = 1`
    the step adds `a * b + cy` into the limb `o`, with `σ = -1` it subtracts. -/
def LimbAcc (σ : ℤ)
    (step : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 × BitVec 64) :
    Prop :=
  ∀ o a b cy : BitVec 64,
    ((step o a b cy).1.toNat : ℤ) + σ * (2 ^ 64 * (step o a b cy).2.toNat)
      = (o.toNat : ℤ) + σ * ((a.toNat : ℤ) * b.toNat + cy.toNat)

/-- `addmulLimb` accumulates with sign `+1`. -/
theorem addmulLimb_acc : LimbAcc 1 addmulLimb := by
  intro o a b cy
  have h := addmulLimb_val o a b cy
  have : ((addmulLimb o a b cy).1.toNat : ℤ)
      + 2 ^ 64 * (addmulLimb o a b cy).2.toNat
      = (o.toNat : ℤ) + ((a.toNat : ℤ) * b.toNat + cy.toNat) := by
    exact_mod_cast congrArg (Nat.cast : Nat → ℤ) h
  linarith

/-- `submulLimb` accumulates with sign `-1`. -/
theorem submulLimb_acc : LimbAcc (-1) submulLimb := by
  intro o a b cy
  have h := submulLimb_val o a b cy
  have : ((submulLimb o a b cy).1.toNat : ℤ)
      + ((a.toNat : ℤ) * b.toNat + cy.toNat)
      = (o.toNat : ℤ) + 2 ^ 64 * (submulLimb o a b cy).2.toNat := by
    exact_mod_cast congrArg (Nat.cast : Nat → ℤ) h
  linarith

/-- One trip of the emitted loop on the accumulator array: read the carry-in
    from the carry cell `cn`, the accumulator limb from cell `t` and the
    multiplicand limb from `up[t]`, write the step's low word back to cell `t`
    and the carry-out to cell `cn`. -/
def accStep {NR NU : Nat}
    (step : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 × BitVec 64)
    (up : Fin NU → BitVec 64) (b : BitVec 64) (cn : Nat)
    (acc : Fin NR → BitVec 64) (t : Nat) : Fin NR → BitVec 64 :=
  memSetDyn
    (memSetDyn acc t (step (memGetDyn acc t) (memGetDyn up t) b (memGetDyn acc cn)).1)
    cn (step (memGetDyn acc t) (memGetDyn up t) b (memGetDyn acc cn)).2

/-- The `n`-fold of `accStep` over the trip indices `0, …, n-1`: the
    `(List.range n).foldl` shape `JLoopBodyN.denote` folds the emitted loop body
    in, at accumulator type `.stackArr 64 NR`. -/
def accFold {NR NU : Nat}
    (step : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 × BitVec 64)
    (up : Fin NU → BitVec 64) (b : BitVec 64) (cn : Nat)
    (n : Nat) (acc : Fin NR → BitVec 64) : Fin NR → BitVec 64 :=
  (List.range n).foldl (accStep step up b cn) acc

/-- The fold peels its last trip. -/
theorem accFold_succ {NR NU : Nat}
    {step : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 × BitVec 64}
    (up : Fin NU → BitVec 64) (b : BitVec 64) (cn n : Nat)
    (acc : Fin NR → BitVec 64) :
    accFold step up b cn (n + 1) acc = accStep step up b cn (accFold step up b cn n acc) n := by
  simp [accFold, List.range_succ, List.foldl_append]

/-- Trip `t` touches only cell `t` and the carry cell. -/
theorem accStep_frame {NR NU : Nat}
    {step : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 × BitVec 64}
    (up : Fin NU → BitVec 64) (b : BitVec 64) (cn : Nat)
    (acc : Fin NR → BitVec 64) (t j : Nat) (ht : t < NR) (hcn : cn < NR) (hj : j < NR)
    (hjt : j ≠ t) (hjc : j ≠ cn) :
    memGetDyn (accStep step up b cn acc t) j = memGetDyn acc j := by
  rw [accStep, memGetDyn_memSetDyn_ne _ cn j _ hcn hj hjc,
    memGetDyn_memSetDyn_ne _ t j _ ht hj hjt]

/-- Cells at or above the trip count, other than the carry cell, still hold
    their entry values. -/
theorem accFold_untouched {NR NU : Nat}
    {step : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 × BitVec 64}
    (up : Fin NU → BitVec 64) (b : BitVec 64) (cn : Nat) (hcn : cn < NR)
    (acc : Fin NR → BitVec 64) :
    ∀ n : Nat, n ≤ cn → ∀ j : Nat, n ≤ j → j < NR → j ≠ cn →
      memGetDyn (accFold step up b cn n acc) j = memGetDyn acc j := by
  intro n
  induction n with
  | zero => intro _ j _ _ _; simp [accFold]
  | succ k ih =>
      intro hk j hj hjr hjc
      rw [accFold_succ,
        accStep_frame up b cn _ k j (by omega) hcn hjr (by omega) hjc]
      exact ih (by omega) j (by omega) hjr hjc

/-- The prefix below the trip index is unchanged by that trip. -/
theorem accStep_cells {NR NU : Nat}
    {step : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 × BitVec 64}
    (up : Fin NU → BitVec 64) (b : BitVec 64) (cn : Nat)
    (acc : Fin NR → BitVec 64) (t : Nat) (ht : t < NR) (hcn : cn < NR) (htc : t ≤ cn) :
    cells (accStep step up b cn acc t) t = cells acc t := by
  simp only [cells, List.map_inj_left, List.mem_range]
  intro j hj
  exact accStep_frame up b cn acc t j ht hcn (by omega) (by omega) (by omega)

/-- **The carry-chain loop invariant.** After `n` trips the accumulator's cells
    `0, …, n-1` hold the accumulated words and the carry cell `cn` holds the
    carry-out:
    `value (rp'[0..n)) + σ · 2^(64n) · carry-out
       = value (rp[0..n)) + σ · (value (up[0..n)) · b + carry-in)`,
    for any step satisfying the signed per-limb identity `LimbAcc σ`. -/
theorem accFold_val {NR NU : Nat} (σ : ℤ)
    {step : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 × BitVec 64}
    (hstep : LimbAcc σ step)
    (up : Fin NU → BitVec 64) (b : BitVec 64) (cn : Nat) (hcn : cn < NR)
    (acc : Fin NR → BitVec 64) :
    ∀ n : Nat, n ≤ cn →
      (bignumVal (cells (accFold step up b cn n acc) n) : ℤ)
          + σ * ((2 ^ 64) ^ n * (memGetDyn (accFold step up b cn n acc) cn).toNat)
        = (bignumVal (cells acc n) : ℤ)
          + σ * ((bignumVal (cells up n) : ℤ) * b.toNat + (memGetDyn acc cn).toNat) := by
  intro n
  induction n with
  | zero => intro _; simp [accFold, cells, bignumVal]
  | succ k ih =>
      intro hk
      have hkc : k < cn := by omega
      have hkr : k < NR := by omega
      set F : Fin NR → BitVec 64 := accFold step up b cn k acc with hF
      have hIH := ih (by omega)
      set r := step (memGetDyn F k) (memGetDyn up k) b (memGetDyn F cn) with hr
      have hlow : memGetDyn (accStep step up b cn F k) k = r.1 := by
        rw [accStep, memGetDyn_memSetDyn_ne _ cn k _ hcn hkr (by omega),
          memGetDyn_memSetDyn_self _ k _ hkr]
      have hhigh : memGetDyn (accStep step up b cn F k) cn = r.2 :=
        memGetDyn_memSetDyn_self _ cn _ hcn
      have hFk : memGetDyn F k = memGetDyn acc k :=
        accFold_untouched up b cn hcn acc k (by omega) k (le_refl k) hkr (by omega)
      have hst := hstep (memGetDyn F k) (memGetDyn up k) b (memGetDyn F cn)
      rw [← hr] at hst
      rw [accFold_succ, cells_succ (accStep step up b cn F k) k, bignumVal_snoc,
        accStep_cells up b cn F k hkr hcn (by omega), hlow, hhigh,
        cells_succ acc k, bignumVal_snoc, cells_succ up k, bignumVal_snoc,
        cells_length, cells_length, cells_length]
      push_cast
      rw [hFk] at hst
      linear_combination hIH + ((2 : ℤ) ^ 64) ^ k * hst

/-- The `mpn_addmul_1` loop invariant: the accumulated words plus the carry
    limb at weight `2^(64n)` are `rp[0..n) + up[0..n) · b + carry-in`. -/
theorem addmulFold_val {NR NU : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (cn : Nat) (hcn : cn < NR) (acc : Fin NR → BitVec 64) (n : Nat) (hn : n ≤ cn) :
    (bignumVal (cells (accFold addmulLimb up b cn n acc) n) : ℤ)
        + (2 ^ 64) ^ n * (memGetDyn (accFold addmulLimb up b cn n acc) cn).toNat
      = (bignumVal (cells acc n) : ℤ)
        + ((bignumVal (cells up n) : ℤ) * b.toNat + (memGetDyn acc cn).toNat) := by
  have h := accFold_val 1 addmulLimb_acc up b cn hcn acc n hn
  linarith

/-- The `mpn_submul_1` loop invariant: the accumulated words plus
    `up[0..n) · b + carry-in` are `rp[0..n)` plus the borrow limb at weight
    `2^(64n)`. -/
theorem submulFold_val {NR NU : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (cn : Nat) (hcn : cn < NR) (acc : Fin NR → BitVec 64) (n : Nat) (hn : n ≤ cn) :
    (bignumVal (cells (accFold submulLimb up b cn n acc) n) : ℤ)
        + ((bignumVal (cells up n) : ℤ) * b.toNat + (memGetDyn acc cn).toNat)
      = (bignumVal (cells acc n) : ℤ)
        + (2 ^ 64) ^ n * (memGetDyn (accFold submulLimb up b cn n acc) cn).toNat := by
  have h := accFold_val (-1) submulLimb_acc up b cn hcn acc n hn
  linarith

/-- Carry-in `0`: the `mpn_addmul_1` contract, with the carry limb in cell
    `cn`. -/
theorem addmulFold_val_zero {NR NU : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (cn : Nat) (hcn : cn < NR) (acc : Fin NR → BitVec 64) (n : Nat) (hn : n ≤ cn)
    (h0 : memGetDyn acc cn = 0) :
    (bignumVal (cells (accFold addmulLimb up b cn n acc) n) : ℤ)
        + (2 ^ 64) ^ n * (memGetDyn (accFold addmulLimb up b cn n acc) cn).toNat
      = (bignumVal (cells acc n) : ℤ) + (bignumVal (cells up n) : ℤ) * b.toNat := by
  have h := addmulFold_val up b cn hcn acc n hn
  rw [h0] at h
  simpa using h

/-- Carry-in `0`: the `mpn_submul_1` contract, with the borrow limb in cell
    `cn`. -/
theorem submulFold_val_zero {NR NU : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (cn : Nat) (hcn : cn < NR) (acc : Fin NR → BitVec 64) (n : Nat) (hn : n ≤ cn)
    (h0 : memGetDyn acc cn = 0) :
    (bignumVal (cells (accFold submulLimb up b cn n acc) n) : ℤ)
        + (bignumVal (cells up n) : ℤ) * b.toNat
      = (bignumVal (cells acc n) : ℤ)
        + (2 ^ 64) ^ n * (memGetDyn (accFold submulLimb up b cn n acc) cn).toNat := by
  have h := submulFold_val up b cn hcn acc n hn
  rw [h0] at h
  simpa using h

/-! ## 3. The loop bodies as covered `LowCT`

Both bodies run over the catCryptDialect context
`Gbody = [rp : .memref NR, idx : .sword 64, up : .memref NU, nlimbs : .sword 64,
          v : .sword 64]` —
the accumulator array, the runtime loop index, then the three invariants. All
arithmetic is in the `srcClean` `SExpr` fragment (`SMul`, `SMulHiU`, `SAdd`,
`SSub`, `SAnd`, `SXor`, `SShr`), so `translateDialectControl` covers it. -/

/-- The prefix both bodies share: read the carry-in from the carry cell
    `rp[nlimbs]`, the accumulator limb from `rp[idx]` and the multiplicand limb
    from `up[idx]`, form the widening product `hi:lo = t * v`, add the carry into
    the low word and synthesise that carry-out branch-free. -/
def limbPrefix : List LowCT :=
  [ .RArrLoad ⟨"cy", .TU64⟩ rpLoc "nlimbs"
  , .RArrLoad ⟨"o", .TU64⟩ rpLoc "idx"
  , .RArrLoad ⟨"t", .TU64⟩ upLoc "idx"
  , .RScalarSetExpr "lo" (.SMul (sv "t") (sv "v"))
  , .RScalarSetExpr "hi" (.SMulHiU (sv "t") (sv "v"))
  , .RScalarSetExpr "s" (.SAdd (sv "lo") (sv "cy")) ]
  ++ ltuCmds "c" (sv "s") (sv "lo")

/-- One `mpn_addmul_1` limb at the runtime loop index: the shared prefix, then
    add the accumulator limb into the low word, fold both carry bits into the
    high word, and store the low word to `rp[idx]` and the carry to
    `rp[nlimbs]`. -/
def addmulBodyLowCT : LowCT := seqAll (
  limbPrefix
  ++ [ LowCT.RScalarSetExpr "u" (.SAdd (sv "s") (sv "o")) ]
  ++ ltuCmds "d" (sv "u") (sv "s")
  ++ [ LowCT.RScalarSetExpr "cyo" (.SAdd (.SAdd (sv "hi") (sv "c")) (sv "d"))
     , .RArrStore rpLoc "idx" ⟨"u", .TU64⟩
     , .RArrStore rpLoc "nlimbs" ⟨"cyo", .TU64⟩ ])

/-- One `mpn_submul_1` limb at the runtime loop index: the shared prefix, then
    subtract the low word from the accumulator limb, fold the carry and borrow
    bits into the high word, and store the difference to `rp[idx]` and the carry
    to `rp[nlimbs]`. -/
def submulBodyLowCT : LowCT := seqAll (
  limbPrefix
  ++ [ LowCT.RScalarSetExpr "u" (.SSub (sv "o") (sv "s")) ]
  ++ ltuCmds "d" (sv "o") (sv "s")
  ++ [ LowCT.RScalarSetExpr "cyo" (.SAdd (.SAdd (sv "hi") (sv "c")) (sv "d"))
     , .RArrStore rpLoc "idx" ⟨"u", .TU64⟩
     , .RArrStore rpLoc "nlimbs" ⟨"cyo", .TU64⟩ ])

/-- The loop-body context: accumulator `rp`, runtime loop index, then the scalar
    multiplier `v`, the limb count `nlimbs` and the multiplicand array `up` as
    invariants. -/
def Gbody : Ctx := [.memref NR, .sword 64, .memref NU, .sword 64, .sword 64]

/-- The body `VarMap`: `v` bound deepest, then `nlimbs`, `up`, `idx`, then `rp`
    at `.here`. -/
def vmBody : VarMap Gbody :=
  (((((VarMap.empty.bind (t := .sword 64) "v").bind
      (t := .sword 64) "nlimbs").bind
      (t := .memref NU) "up").bind
      (t := .sword 64) "idx").bind (t := .memref NR) "rp")

/-! ## 4. The runtime-trip loop programs

Outer argument context `[v, n, up, rp]` (newest first), routing
`rp → RDI`, `up → RSI`, `n → RDX`, `v → RCX`. The limb count `n` is both the
runtime trip count and a loop invariant: the body indexes the carry cell by
it. -/

/-- The runtime trip count `n` (RDX). -/
def accCount : Ctxt.Var Gouter r64 := .there .here

/-- The accumulator seed: the output array `rp` (RDI). -/
def accInit : Ctxt.Var Gouter AR := .there (.there (.there .here))

/-- The loop invariants: the multiplicand array `up` (RSI), the limb count `n`
    (RDX) and the scalar multiplier `v` (RCX). Invariant `i` is outer argument
    `i + 1`, the order the looped ABI export's base-name derivation expects. -/
def accInvs : HVector (fun ty => Ctxt.Var Gouter ty) [AU, r64, r64] :=
  .cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))

/-- The front-compiled runtime-trip `mpn_addmul_1`: one body copy behind a `jne`
    back-edge, the trip counter seeded from the runtime `n` register, the output
    array threaded as the loop accumulator and `up`/`n`/`v` as loop invariants.
    `none` if the front declines. -/
def addmulRtProgOpt : Option (ComL Gouter AR) :=
  rolledForLoopNRt (Γouter := Gouter) (accCTy := .memref NR)
    (invCTys := [.memref NU, .sword 64, .sword 64])
    vmBody "rp" addmulBodyLowCT accCount accInit accInvs

/-- The front-compiled runtime-trip `mpn_submul_1`, in the same shape.
    `none` if the front declines. -/
def submulRtProgOpt : Option (ComL Gouter AR) :=
  rolledForLoopNRt (Γouter := Gouter) (accCTy := .memref NR)
    (invCTys := [.memref NU, .sword 64, .sword 64])
    vmBody "rp" submulBodyLowCT accCount accInit accInvs

-- The front accepts both bodies and wraps each in a `ComL.forLoopNRt`.
#guard addmulRtProgOpt.isSome
#guard submulRtProgOpt.isSome

/-- **The emitted `mpn_addmul_1` loop's denotation is the `JLoopBodyN` fold of
    the front body.** Whenever the front compiles `addmulBodyLowCT` to `update`,
    the runtime-trip program's denotation at any valuation is the `n`-fold of
    `update` over the trip indices, seeded by the `rp` argument and threading
    `up`, `n` and `v`. The instance of `rolledForLoopNRt_denote` at this
    kernel. -/
theorem addmulRtProg_denote
    {update : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.memref NR :: .sword 64 ::
        [CryptoTy.memref NU, CryptoTy.sword 64, CryptoTy.sword 64]))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NR))}
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJ
      (accCTy := .memref NR) vmBody "rp" addmulBodyLowCT = some update)
    (V : Ctxt.Valuation Gouter) :
    addmulRtProgOpt.map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(accCount.lookup V).toNat, update⟩
          (Expr.lookupArgs accInvs V) (accInit.lookup V)) :=
  rolledForLoopNRt_denote vmBody "rp" addmulBodyLowCT accCount accInit accInvs
    hupd V

/-- **The emitted `mpn_submul_1` loop's denotation is the `JLoopBodyN` fold of
    the front body.** The instance of `rolledForLoopNRt_denote` at the
    multiply-subtract kernel. -/
theorem submulRtProg_denote
    {update : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.memref NR :: .sword 64 ::
        [CryptoTy.memref NU, CryptoTy.sword 64, CryptoTy.sword 64]))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NR))}
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJ
      (accCTy := .memref NR) vmBody "rp" submulBodyLowCT = some update)
    (V : Ctxt.Valuation Gouter) :
    submulRtProgOpt.map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(accCount.lookup V).toNat, update⟩
          (Expr.lookupArgs accInvs V) (accInit.lookup V)) :=
  rolledForLoopNRt_denote vmBody "rp" submulBodyLowCT accCount accInit accInvs
    hupd V

/-! ## 5. The owned `Lprog`s and the rendered `.s` -/

/-- The rolled, owned-RA 4-argument-ABI `Lprog` for a front-compiled runtime-trip
    kernel under the C symbol `fname` (`RDI = rp`, `RSI = up`, `RDX = n`,
    `RCX = v`).

    The `MULXHI` high-word binding the front emits for `SMulHiU` is coalesced
    with its paired low `MUL` into the printer's two-output `mulx` by
    `FuseMulHi.fuseMulHiLprog` in its `saveRdx` looped-body mode: the
    kernel's multiply sits inside a back-edge, so `%rdx` is saved and restored
    around the pinned multiplicand. -/
def rtLprogOpt (prog : Option (ComL Gouter AR)) (fname : String) : Option Lprog :=
  prog.map (fun c =>
    FuseMulHi.fuseMulHiLprog
      (ComL.toLprogPhysAbi c fname (argName 0) [argName 1]
        (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64])
      (saveRdx := true))

/-- The 4-argument-ABI physical body of a front-compiled runtime-count loop. -/
def rtPhysBodyOpt (prog : Option (ComL Gouter AR)) : Option Lcmd :=
  prog.map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"]
      [64, 64, 64, 64]).lfd_body)

/-- The owned AT&T `.s` text for the runtime-trip `mpn_addmul_1`. -/
def addmulRtAsmOpt (fname : String) : Option String :=
  (rtLprogOpt addmulRtProgOpt fname).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

/-- The owned AT&T `.s` text for the runtime-trip `mpn_submul_1`. -/
def submulRtAsmOpt (fname : String) : Option String :=
  (rtLprogOpt submulRtProgOpt fname).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

-- Each physical body carries a real back-edge: an internal label and a
-- conditional jump, so the emit is a counted loop and not an unrolled chain.
#guard ((rtPhysBodyOpt addmulRtProgOpt).map (fun body =>
  (body.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
    && (body.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false))))
  = some true
#guard ((rtPhysBodyOpt submulRtProgOpt).map (fun body =>
  (body.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
    && (body.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false))))
  = some true

-- Rendered-asm correctness is the external GMP KAT; an in-Lean strContains check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 6. Emit driver

The renders are written while this module elaborates, so `lake` produces them
from this file and no separate driver or Makefile rule carries the
dependency. -/

/-- Write the owned-backend `.s` for both runtime-trip kernels into the
    `bench/mpn_addmul_1_front_compare/gen_com` harness directory. -/
def emitMain : IO Unit := do
  let dir := "bench/mpn_addmul_1_front_compare/gen_com"
  IO.FS.createDirAll dir
  match addmulRtAsmOpt "mpn_addmul_1_rt", submulRtAsmOpt "mpn_submul_1_rt" with
  | some a, some s =>
      IO.FS.writeFile (dir ++ "/mpn_addmul_1_rt_owned.s") a
      IO.FS.writeFile (dir ++ "/mpn_submul_1_rt_owned.s") s
      IO.println "WROTE bench/mpn_addmul_1_front_compare/gen_com/mpn_addmul_1_rt_owned.s"
      IO.println "WROTE bench/mpn_addmul_1_front_compare/gen_com/mpn_submul_1_rt_owned.s"
  | _, _ => throw (IO.userError "the runtime-loop front declined a kernel")

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontEmit
