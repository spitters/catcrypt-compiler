/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
public import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
public meta import CatCrypt.Crypto.SecureCompilation.VIR.MontMulFragmentDemo
public import CatCrypt.Crypto.SecureCompilation.VIR.MontMulFragmentDemo
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi

/-!
# `mpn_mul_1` as a front-generated runtime-trip loop

`mpn_mul_1(rp, up, n, v)` sets `rp[0..n) = up[0..n) * v` and returns the top
carry limb. This module sources that kernel through the verified runtime-loop
front: the per-limb body is covered `LowCT`
(`RArrLoad` / `RScalarSetExpr` / `RArrStore` over the runtime loop index), and
`Dialects.TranslateDialectRuntimeLoop.rolledForLoopNRt` front-compiles it
(`translateDialectControl` + `cryptoDialectToJasminCom`) and wraps it in a
`ComL.forLoopNRt` — one body copy behind a `jne` back-edge, the trip counter
seeded from the runtime `n` register.

```
  limbBodyLowCT (RArrLoad rp/up at idx, SMul/SMulHiU/SAdd/bSltu carry step,
                 RArrStore rp at idx and idx+1)
    --(rolledForLoopNRt)--> JLoopBodyN.update : Com jasminDialect [AR, reg 64, reg 64, AU] AR
    --(ComL.forLoopNRt update n rp [v, up] (ret rp))--> ComL
    --(ComL.toLprogPhysAbi / renderLprogAtt)-----------> AT&T .s
```

## The carry cell

The loop-carried accumulator is the whole output array `rp`; the running carry
rides in cell `idx` of that array. At trip `idx` the body reads `rp[idx]` as the
carry-in, writes the product's low word back to `rp[idx]`, and writes the new
carry to `rp[idx + 1]`. After `n` trips `rp[0..n)` holds the low words and
`rp[n]` holds the carry-out — the `rp[n] = mpn_mul_1(rp, up, n, v)` shape a
schoolbook `mpn_mul` uses. The caller zeroes `rp[0]` to seed a carry-in of `0`.

## ABI

```c
extern uint64_t *mpn_mul_1_rt(uint64_t *rp, const uint64_t *up, uint64_t n, uint64_t v);
```

`rp` (RDI), `up` (RSI), `n` (RDX), `v` (RCX). `rp` holds `n + 1` words.

## Main results

* `mul1Limb_val`: the per-limb identity `low + 2^64 · carry-out = a · b + cy`.
* `mulLimbs_val`: the carry chain over a limb list,
  `bignumVal (mulLimbs as b cy) = bignumVal as * b + cy`.
* `mul1Fold_val`: the loop invariant over the memref carrier — after `n` trips,
  `carry · 2^(64n) + value (rp[0..n)) = value (up[0..n)) · b + carry-in`, for
  every `NR` and `NU`.
* `mul1Fold_val_zero`: the same at carry-in zero, the caller's contract.
* `mul1RtProg_denote`: the runtime-trip loop program's denotation as the fold.

## Arithmetic

`mul1Limb` is the per-limb word step and `mulLimbs` its carry chain over a limb
list; `mulLimbs_val` is the multi-precision identity
`bignumVal (mulLimbs as b cy) = bignumVal as * b + cy`. `mul1FoldStep` /
`mul1Fold` are the same step and chain over the memref carrier, in the
`(List.range n).foldl` shape `JLoopBodyN.denote` folds the emitted body in, and
`mul1Fold_val` is the loop invariant
`carry · 2^(64n) + value (rp[0..n)) = value (up[0..n)) · b + carry-in`
read off the accumulator's first `n + 1` cells.

The carry-out bit is synthesised branch-free by `FieldReduceIdioms.bSltu`
(`(~x & y) | (~(x ^ y) & (x - y))) >> 63`), the shape the covered `SExpr`
fragment admits: `SLt` has no dialect lowering and `srcClean` excludes it.

## Scope

`mul1Limb_val`, `mulLimbs_val` and `mul1Fold_val` hold for every `NR` / `NU`;
`NU` fixes only the memref width of the concrete front-compiled instance below,
whose rendered SIB accesses are byte-offset and so size-agnostic.

`mul1RtProg_denote` carries the front-compilation hypothesis
`frontLoopBodyJ … = some update` and concludes at `JLoopBodyN.denote` of that
`update`. Identifying that denotation with `mul1FoldStep` — so that
`mul1Fold_val` reads as a statement about the emitted kernel — is the separate
source-preservation step (`translateDialectControl_denote_ctl` composed with
`cryptoDialectToJasminCom`), not established here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit

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
  (mulHiW_toNat mulHiW_le mulx_reconstruct)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-! ## 1. The per-limb word step and its carry chain -/

/-- One `mpn_mul_1` limb step on words: multiply limb `a` by the scalar `b`, add
    the running carry `cy`, and split into `(low word, carry-out)`. The carry-out
    bit of `a * b + cy` is the branch-free `bSltu` of the low sum against the
    product's low word. -/
def mul1Limb (a b cy : BitVec 64) : BitVec 64 × BitVec 64 :=
  (a * b + cy, mulHiW a b + bSltu (a * b + cy) (a * b))

/-- The carry-out bit of `x + cy` is `1` exactly when the unbounded sum reaches
    `2 ^ 64`, and the low word is the sum reduced. -/
theorem addCarry_split (x cy : BitVec 64) :
    (x + cy).toNat + 2 ^ 64 * (bSltu (x + cy) x).toNat = x.toNat + cy.toNat := by
  have hx := x.isLt
  have hcy := cy.isLt
  have hsum : (x + cy).toNat = (x.toNat + cy.toNat) % 2 ^ 64 := by
    simp [BitVec.toNat_add]
  rw [bSltu_eq]
  by_cases h : 2 ^ 64 ≤ x.toNat + cy.toNat
  · have hlt : (x + cy).ult x = true := by
      simp only [BitVec.ult, decide_eq_true_eq, hsum]
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [if_pos hlt, hsum, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    simp only [show ((1 : BitVec 64).toNat) = 1 from rfl]
    omega
  · have hlt : (x + cy).ult x = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not, hsum, Nat.not_lt]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [if_neg (by simp [hlt]), hsum, Nat.mod_eq_of_lt (by omega)]
    simp only [show ((0 : BitVec 64).toNat) = 0 from rfl]
    omega

/-- The carry-out bit is `0` or `1`. -/
theorem bSltu_le_one (x y : BitVec 64) : (bSltu x y).toNat ≤ 1 := by
  rw [bSltu_eq]; split <;> simp

/-- **The single-limb multiply identity.** `mul1Limb a b cy` splits `a * b + cy`
    into a low word and a carry-out word:
    `low + 2 ^ 64 * carry-out = a * b + cy`. -/
theorem mul1Limb_val (a b cy : BitVec 64) :
    (mul1Limb a b cy).1.toNat + 2 ^ 64 * (mul1Limb a b cy).2.toNat
      = a.toNat * b.toNat + cy.toNat := by
  have hprod := mulx_reconstruct a b
  have hsplit := addCarry_split (a * b) cy
  have hcle := bSltu_le_one (a * b + cy) (a * b)
  have hhile := mulHiW_le a b
  have hno : (mulHiW a b + bSltu (a * b + cy) (a * b)).toNat
      = (mulHiW a b).toNat + (bSltu (a * b + cy) (a * b)).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  simp only [mul1Limb, hno]
  omega

/-- The carry chain of `mpn_mul_1` over a limb list: the low words of
    `as * b + cy`, with the final carry-out as the top limb. The list-level twin
    of `MultiLimbKernel.addLimbs`. -/
def mulLimbs : List (BitVec 64) → BitVec 64 → BitVec 64 → List (BitVec 64)
  | a :: as, b, cy =>
      (mul1Limb a b cy).1 :: mulLimbs as b (mul1Limb a b cy).2
  | [], _, cy => [cy]

/-- **The multi-precision single-limb multiplication identity.** The carry chain
    computes the exact integer product `as * b + cy`, low limb to high, with the
    final carry on top. -/
theorem mulLimbs_val : ∀ (as : List (BitVec 64)) (b cy : BitVec 64),
    bignumVal (mulLimbs as b cy) = bignumVal as * b.toNat + cy.toNat
  | [], b, cy => by simp [mulLimbs, bignumVal]
  | a :: as, b, cy => by
      have ih := mulLimbs_val as b (mul1Limb a b cy).2
      have hstep := mul1Limb_val a b cy
      simp only [mulLimbs, bignumVal, ih]
      have hexpand : (a.toNat + 2 ^ 64 * bignumVal as) * b.toNat
          = a.toNat * b.toNat + 2 ^ 64 * (bignumVal as * b.toNat) := by ring
      rw [hexpand]
      omega

/-- Carry-in `0`: the low words plus the top carry are exactly `as * b`. -/
theorem mulLimbs_val_zero (as : List (BitVec 64)) (b : BitVec 64) :
    bignumVal (mulLimbs as b 0) = bignumVal as * b.toNat := by
  simpa using mulLimbs_val as b 0

/-- The chain has one more limb than the input: `n` low words and the carry. -/
theorem mulLimbs_length : ∀ (as : List (BitVec 64)) (b cy : BitVec 64),
    (mulLimbs as b cy).length = as.length + 1
  | [], _, _ => rfl
  | a :: as, b, cy => by
      simp [mulLimbs, mulLimbs_length as b (mul1Limb a b cy).2]

/-! ## 2. The same chain over the memref carrier

The emitted loop carries the whole output array as its accumulator and folds one
body copy over the trip indices. `mul1FoldStep` is that body's word-level effect
and `mul1Fold` the `(List.range n).foldl` shape `JLoopBodyN.denote` uses. -/

/-- The first `k` cells of a memref as a little-endian limb list. -/
def cells {N : Nat} (arr : Fin N → BitVec 64) (k : Nat) : List (BitVec 64) :=
  (List.range k).map (fun j => memGetDyn arr j)

/-- `cells` of a successor length appends the next cell. -/
theorem cells_succ {N : Nat} (arr : Fin N → BitVec 64) (k : Nat) :
    cells arr (k + 1) = cells arr k ++ [memGetDyn arr k] := by
  simp [cells, List.range_succ]

/-- `cells arr k` has length `k`. -/
theorem cells_length {N : Nat} (arr : Fin N → BitVec 64) (k : Nat) :
    (cells arr k).length = k := by simp [cells]

/-- A memref write at index `k` is invisible at any other in-range index. -/
theorem memGetDyn_memSetDyn_ne {N : Nat} (arr : Fin N → BitVec 64)
    (k l : Nat) (v : BitVec 64) (hk : k < N) (hl : l < N) (hne : l ≠ k) :
    memGetDyn (memSetDyn arr k v) l = memGetDyn arr l := by
  match N, arr with
  | 0, _ => exact absurd hk (Nat.not_lt_zero k)
  | (m + 1), arr =>
      simp only [memGetDyn, memSetDyn, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl]
      rw [if_neg (by simp only [Fin.mk.injEq]; omega)]

/-- A memref write at an in-range index reads back at that index. -/
theorem memGetDyn_memSetDyn_self {N : Nat} (arr : Fin N → BitVec 64)
    (k : Nat) (v : BitVec 64) (hk : k < N) :
    memGetDyn (memSetDyn arr k v) k = v := by
  match N, arr with
  | 0, _ => exact absurd hk (Nat.not_lt_zero k)
  | (m + 1), arr =>
      simp only [memGetDyn, memSetDyn, Nat.mod_eq_of_lt hk]
      simp

/-- One trip of the emitted loop on the accumulator array: read the carry-in from
    cell `t`, the multiplicand limb from `up[t]`, write the product's low word
    back to cell `t` and the carry-out to cell `t + 1`. -/
def mul1FoldStep {NR NU : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) (t : Nat) : Fin NR → BitVec 64 :=
  memSetDyn (memSetDyn acc t (mul1Limb (memGetDyn up t) b (memGetDyn acc t)).1)
    (t + 1) (mul1Limb (memGetDyn up t) b (memGetDyn acc t)).2

/-- The `n`-fold of `mul1FoldStep` over the trip indices `0, …, n-1`: the
    `(List.range n).foldl` shape `JLoopBodyN.denote` folds the emitted loop body
    in, at accumulator type `.stackArr 64 NR`. -/
def mul1Fold {NR NU : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (n : Nat) (acc : Fin NR → BitVec 64) : Fin NR → BitVec 64 :=
  (List.range n).foldl (mul1FoldStep up b) acc

/-- The fold peels its last trip. -/
theorem mul1Fold_succ {NR NU : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (n : Nat) (acc : Fin NR → BitVec 64) :
    mul1Fold up b (n + 1) acc = mul1FoldStep up b (mul1Fold up b n acc) n := by
  simp [mul1Fold, List.range_succ, List.foldl_append]

/-- Cells strictly below the trip index are already final: trip `t` writes only
    cells `t` and `t + 1`. -/
theorem mul1FoldStep_frame {NR NU : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) (t j : Nat) (ht : t + 1 < NR) (hj : j < t) :
    memGetDyn (mul1FoldStep up b acc t) j = memGetDyn acc j := by
  rw [mul1FoldStep,
    memGetDyn_memSetDyn_ne _ (t + 1) j _ ht (by omega) (by omega),
    memGetDyn_memSetDyn_ne _ t j _ (by omega) (by omega) (by omega)]

/-- The whole prefix below the trip index is unchanged. -/
theorem mul1FoldStep_cells {NR NU : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) (t : Nat) (ht : t + 1 < NR) :
    cells (mul1FoldStep up b acc t) t = cells acc t := by
  simp only [cells, List.map_inj_left, List.mem_range]
  intro j hj
  exact mul1FoldStep_frame up b acc t j ht hj

/-- **The carry-chain loop invariant.** After `n` trips the accumulator's first
    `n + 1` cells hold `up[0..n) * b` plus the seeded carry-in `acc[0]`: the low
    words in cells `0, …, n-1` and the carry-out in cell `n`. This is the
    invariant
    `carry · 2^(64n) + value (rp[0..n)) = value (up[0..n)) · b + carry-in`,
    stated as one `bignumVal` over the `n + 1` cells. -/
theorem mul1Fold_val {NR NU : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) :
    ∀ n : Nat, n < NR →
      bignumVal (cells (mul1Fold up b n acc) (n + 1))
        = bignumVal (cells up n) * b.toNat + (memGetDyn acc 0).toNat := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [mul1Fold, cells, bignumVal]
  | succ k ih =>
      intro hkr
      have hkr' : k < NR := by omega
      set F : Fin NR → BitVec 64 := mul1Fold up b k acc with hF
      have hIH := ih hkr'
      -- the two cells trip `k` writes are the two words of the limb step
      have hlow : memGetDyn (mul1FoldStep up b F k) k
          = (mul1Limb (memGetDyn up k) b (memGetDyn F k)).1 := by
        rw [mul1FoldStep,
          memGetDyn_memSetDyn_ne _ (k + 1) k _ hkr (by omega) (by omega),
          memGetDyn_memSetDyn_self _ k _ (by omega)]
      have hhigh : memGetDyn (mul1FoldStep up b F k) (k + 1)
          = (mul1Limb (memGetDyn up k) b (memGetDyn F k)).2 :=
        memGetDyn_memSetDyn_self _ (k + 1) _ hkr
      have hstep := mul1Limb_val (memGetDyn up k) b (memGetDyn F k)
      -- the head-cell contribution, scaled by the prefix weight `(2^64)^k`
      have hkey : (mul1Limb (memGetDyn up k) b (memGetDyn F k)).1.toNat * (2 ^ 64) ^ k
            + (mul1Limb (memGetDyn up k) b (memGetDyn F k)).2.toNat
                * ((2 ^ 64) ^ k * 2 ^ 64)
          = (memGetDyn up k).toNat * b.toNat * (2 ^ 64) ^ k
              + (memGetDyn F k).toNat * (2 ^ 64) ^ k := by
        calc (mul1Limb (memGetDyn up k) b (memGetDyn F k)).1.toNat * (2 ^ 64) ^ k
              + (mul1Limb (memGetDyn up k) b (memGetDyn F k)).2.toNat
                  * ((2 ^ 64) ^ k * 2 ^ 64)
            = ((mul1Limb (memGetDyn up k) b (memGetDyn F k)).1.toNat
                + 2 ^ 64 * (mul1Limb (memGetDyn up k) b (memGetDyn F k)).2.toNat)
              * (2 ^ 64) ^ k := by ring
          _ = ((memGetDyn up k).toNat * b.toNat + (memGetDyn F k).toNat)
                * (2 ^ 64) ^ k := by rw [hstep]
          _ = (memGetDyn up k).toNat * b.toNat * (2 ^ 64) ^ k
                + (memGetDyn F k).toNat * (2 ^ 64) ^ k := by ring
      rw [mul1Fold_succ,
        cells_succ (mul1FoldStep up b F k) (k + 1),
        cells_succ (mul1FoldStep up b F k) k,
        bignumVal_snoc, bignumVal_snoc]
      simp only [List.length_append, List.length_cons, List.length_nil,
        cells_length, Nat.zero_add]
      rw [mul1FoldStep_cells up b F k hkr, hlow, hhigh,
        cells_succ up k, bignumVal_snoc, cells_length,
        show ((2 : ℕ) ^ 64) ^ (k + 1) = (2 ^ 64) ^ k * 2 ^ 64 from pow_succ _ _]
      rw [cells_succ F k, bignumVal_snoc, cells_length] at hIH
      nlinarith [hIH, hkey]

/-- Carry-in `0`: the emitted loop's accumulator cells `0, …, n` are exactly
    `up[0..n) * b`, with cell `n` the returned carry limb — the `mpn_mul_1`
    contract. -/
theorem mul1Fold_val_zero {NR NU : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) (n : Nat) (hnr : n < NR)
    (h0 : memGetDyn acc 0 = 0) :
    bignumVal (cells (mul1Fold up b n acc) (n + 1))
      = bignumVal (cells up n) * b.toNat := by
  rw [mul1Fold_val up b acc n hnr, h0]
  simp

/-! ## 3. The loop body as covered `LowCT`

The body runs over the catCryptDialect context
`Γbody = [rp : .memref NR, idx : .sword 64, v : .sword 64, up : .memref NU]` —
the accumulator array, the runtime loop index, then the two invariants. All
arithmetic is in the `srcClean` `SExpr` fragment (`SMul`, `SMulHiU`, `SAdd`,
`SSub`, `SAnd`, `SXor`, `SShr`), so `translateDialectControl` covers it. -/

/-- Limb count of the multiplicand array in the denotation model. The rendered
    SIB loads use byte offsets, so the assembly is size-agnostic; this only
    bounds the in-Lean model. The arithmetic results of §1 and §2 are stated for
    every `NU` / `NR`. -/
abbrev NU : Nat := 8

/-- Word count of the output array: `NU` low words plus the carry cell. -/
abbrev NR : Nat := NU + 1

/-- All-ones 64-bit literal. -/
def ones : Nat := 18446744073709551615

/-- Bitwise NOT via XOR with all-ones. -/
def notE (e : SExpr) : SExpr := .SXor e (.SLit ones)

/-- Bitwise OR via `(a ^ b) ^ (a & b)`. -/
def orE (a b : SExpr) : SExpr := .SXor (.SXor a b) (.SAnd a b)

/-- Named scalar-slot read. -/
def sv (n : String) : SExpr := .SVar n

/-- `dst := (x <u y)` as `0`/`1`, branch-free — the `FieldReduceIdioms.bSltu`
    shape in the covered `SExpr` fragment. Scratch slots `dst ++ "q"` /
    `dst ++ "r"`. -/
def ltuCmds (dst : String) (x y : SExpr) : List LowCT :=
  [ .RScalarSetExpr (dst ++ "q") (.SAnd (notE x) y),
    .RScalarSetExpr (dst ++ "r") (.SAnd (notE (.SXor x y)) (.SSub x y)),
    .RScalarSetExpr dst
      (.SShr (orE (.SVar (dst ++ "q")) (.SVar (dst ++ "r"))) (.SLit 63)) ]

/-- Sequence a `LowCT` list into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- The output-array slot `rp` (`NR` words), the loop accumulator. -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * NR)⟩

/-- The multiplicand-array slot `up` (`NU` words), a loop invariant. -/
def upLoc : Located := ⟨"up", .TBytes (8 * NU)⟩

/-- One `mpn_mul_1` limb at the runtime loop index `idx`: read the carry-in from
    `rp[idx]` and the multiplicand limb from `up[idx]`, form the widening product
    `hi:lo = t * v`, add the carry into the low word, synthesise the carry-out
    branch-free, then store the low word to `rp[idx]` and the new carry to
    `rp[idx + 1]`. -/
def limbBodyLowCT : LowCT := seqAll (
  [ .RArrLoad ⟨"cy", .TU64⟩ rpLoc "idx"
  , .RArrLoad ⟨"t", .TU64⟩ upLoc "idx"
  , .RScalarSetExpr "lo" (.SMul (sv "t") (sv "v"))
  , .RScalarSetExpr "hi" (.SMulHiU (sv "t") (sv "v"))
  , .RScalarSetExpr "s" (.SAdd (sv "lo") (sv "cy")) ]
  ++ ltuCmds "c" (sv "s") (sv "lo")
  ++ [ .RScalarSetExpr "cyo" (.SAdd (sv "hi") (sv "c"))
     , .RArrStore rpLoc "idx" ⟨"s", .TU64⟩
     , .RScalarSetExpr "idx1" (.SAdd (sv "idx") (.SLit 1))
     , .RArrStore rpLoc "idx1" ⟨"cyo", .TU64⟩ ])

/-- The loop-body context: accumulator `rp`, runtime loop index, the scalar
    multiplier `v` and the multiplicand array `up` as invariants. -/
def Gbody : Ctx := [.memref NR, .sword 64, .sword 64, .memref NU]

/-- The body `VarMap`: `up` bound deepest, then `v`, then `idx`, then `rp` at
    `.here`. -/
def vmBody : VarMap Gbody :=
  ((((VarMap.empty.bind (t := .memref NU) "up").bind
      (t := .sword 64) "v").bind
      (t := .sword 64) "idx").bind (t := .memref NR) "rp")

/-! ## 4. The runtime-trip loop program

Outer argument context `[v, n, up, rp]` (newest first), routing
`rp → RDI`, `up → RSI`, `n → RDX`, `v → RCX`. -/

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The output-array jasmin type. -/
abbrev AR : JasminTy := .stackArr 64 NR

/-- The multiplicand-array jasmin type. -/
abbrev AU : JasminTy := .stackArr 64 NU

/-- The kernel's outer argument context, newest first. -/
abbrev Gouter : Ctxt jasminDialect := [r64, r64, AU, AR]

/-- The runtime trip count `n` (RDX). -/
def mul1Count : Ctxt.Var Gouter r64 := .there .here

/-- The accumulator seed: the output array `rp` (RDI). -/
def mul1Init : Ctxt.Var Gouter AR := .there (.there (.there .here))

/-- The loop invariants: the scalar multiplier `v` (RCX) and the multiplicand
    array `up` (RSI). -/
def mul1Invs : HVector (fun ty => Ctxt.Var Gouter ty) [r64, AU] :=
  .cons .here (.cons (.there (.there .here)) .nil)

/-- The front-compiled runtime-trip `mpn_mul_1`: one body copy behind a `jne`
    back-edge, the trip counter seeded from the runtime `n` register, the output
    array threaded as the loop accumulator and `v`/`up` as loop invariants.
    `none` if the front declines. -/
def mul1RtProgOpt (_ : Unit) : Option (ComL Gouter AR) :=
  rolledForLoopNRt (Γouter := Gouter) (accCTy := .memref NR)
    (invCTys := [.sword 64, .memref NU])
    vmBody "rp" limbBodyLowCT mul1Count mul1Init mul1Invs

-- The front accepts the body and wraps it in a `ComL.forLoopNRt`.
#guard (mul1RtProgOpt ()).isSome

/-- **The emitted loop's denotation is the `JLoopBodyN` fold of the front body.**
    Whenever the front compiles `limbBodyLowCT` to `update`, the runtime-trip
    program's denotation at any valuation is the `n`-fold of `update` over the
    trip indices, seeded by the `rp` argument and threading `v` and `up`. The
    instance of `rolledForLoopNRt_denote` at this kernel. -/
theorem mul1RtProg_denote
    {update : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.memref NR :: .sword 64 ::
        [CryptoTy.sword 64, CryptoTy.memref NU]))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NR))}
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJ
      (accCTy := .memref NR) vmBody "rp" limbBodyLowCT = some update)
    (V : Ctxt.Valuation Gouter) :
    (mul1RtProgOpt ()).map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(mul1Count.lookup V).toNat, update⟩
          (Expr.lookupArgs mul1Invs V) (mul1Init.lookup V)) :=
  rolledForLoopNRt_denote vmBody "rp" limbBodyLowCT mul1Count mul1Init mul1Invs
    hupd V

/-! ## 5. The owned `Lprog` and the rendered `.s` -/

/-- The rolled, owned-RA 4-argument-ABI `Lprog` for the runtime-trip
    `mpn_mul_1` under the C symbol `fname`
    (`RDI = rp`, `RSI = up`, `RDX = n`, `RCX = v`).

    The `MULXHI` high-word binding the front emits for `SMulHiU` is coalesced
    with its paired low `MUL` into the printer's two-output `mulx` by
    `FuseMulHi.fuseMulHiLprog` in its `saveRdx` looped-body mode: the
    kernel's multiply sits inside a back-edge, so `%rdx` is saved and restored
    around the pinned multiplicand. -/
def mul1RtLprogOpt (fname : String) : Option Lprog :=
  (mul1RtProgOpt ()).map (fun c =>
    FuseMulHi.fuseMulHiLprog
      (ComL.toLprogPhysAbi c fname (argName 0) [argName 1]
        (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64])
      (saveRdx := true))

/-- The render identity this module stamps into its artifact: the Lean module
    that produces the render and the front route the kernel takes. Rendered by
    `LprogAsmPrinter.provenanceTrailer` as the `.ident` trailer of the emitted
    `.s`. -/
def mul1Provenance : LprogAsmPrinter.Provenance :=
  { module := "CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit"
  , route := "rolledForLoopNRt" }

/-- The owned AT&T `.s` text for the runtime-trip `mpn_mul_1`, rendered after the
    `Lprog` optimization pipeline and carrying the `mul1Provenance` trailer. -/
def mul1RtAsmOpt (fname : String) : Option String :=
  (mul1RtLprogOpt fname).map
    (fun p => renderLprogAtt (LprogOptPipeline.optimizeLprog p) (some mul1Provenance))

/-- The 4-argument-ABI physical body of the front-compiled runtime-count loop. -/
def mul1RtPhysBodyOpt (_ : Unit) : Option Lcmd :=
  (mul1RtProgOpt ()).map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"]
      [64, 64, 64, 64]).lfd_body)

-- The physical body carries a real back-edge: an internal label and a
-- conditional jump, so the emit is a counted loop and not an unrolled chain.
#guard ((mul1RtPhysBodyOpt ()).map (fun body =>
  (body.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
    && (body.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false))))
  = some true

/-- The red-zone qsave slot each streaming memref access reloads its SIB base
    from, in body order. Each `LOADIDX`/`STOREIDX` is preceded by the reload of
    its base into `R14`, so the slot names read off the pairs are the array
    argument each access addresses through. -/
def mul1RtReloads (_ : Unit) : List String :=
  match mul1RtPhysBodyOpt () with
  | none => []
  | some body =>
      (body.zip (body.drop 1)).filterMap (fun (prev, cur) =>
        match cur.li_i, prev.li_i with
        | .Lopn _ "LOADIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] =>
            some q
        | .Lopn _ "STOREIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] =>
            some q
        | _, _ => none)

-- `rp` (RDI) and `up` (RSI) are the two pointer arguments; `n` (RDX) and `v`
-- (RCX) are scalars, so no access may reload its base from their qsave slots.
-- The multiplicand load reaches `up` through the `RSI` slot.
#guard (mul1RtReloads ()).contains "qsave.RSI"
#guard (mul1RtReloads ()).all (fun q => q == "qsave.RDI" || q == "qsave.RSI")

-- The rendered text carries the widening multiply and the streaming SIB
-- operands, and emits no `UNHANDLED` sentinel.
#guard ((mul1RtAsmOpt "mpn_mul_1_rt").getD "").length > 0
#guard !(strContains ((mul1RtAsmOpt "mpn_mul_1_rt").getD "") "UNHANDLED")
#guard strContains ((mul1RtAsmOpt "mpn_mul_1_rt").getD "") "mulx"
#guard strContains ((mul1RtAsmOpt "mpn_mul_1_rt").getD "") "(%r14,"

-- The render carries the provenance trailer: the printer's fixed tool marker,
-- this module's name, and the front route.
#guard strContains ((mul1RtAsmOpt "mpn_mul_1_rt").getD "")
  LprogAsmPrinter.provenanceMarker
#guard strContains ((mul1RtAsmOpt "mpn_mul_1_rt").getD "")
  "module=CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit"
#guard strContains ((mul1RtAsmOpt "mpn_mul_1_rt").getD "") "route=rolledForLoopNRt"

/-! ## 6. Emit driver

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

/-- Write the owned-backend `.s` for the runtime-trip `mpn_mul_1` into the
    `bench/mpn_mul_1_front_compare/gen_com` harness directory. -/
def emitMain : IO Unit := do
  let dir := "bench/mpn_mul_1_front_compare/gen_com"
  IO.FS.createDirAll dir
  match mul1RtAsmOpt "mpn_mul_1_rt" with
  | some s =>
      IO.FS.writeFile (dir ++ "/mpn_mul_1_rt_owned.s") s
      IO.println "WROTE bench/mpn_mul_1_front_compare/gen_com/mpn_mul_1_rt_owned.s"
  | none => throw (IO.userError "the runtime-loop front declined mpn_mul_1")

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
