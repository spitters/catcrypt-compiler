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
# `mpn_lshift` / `mpn_rshift` as a front-generated runtime-trip loop

`mpn_lshift(rp, up, n, cnt)` shifts the `n`-limb value at `up` left by `cnt`
bits (`0 < cnt < 64`) and returns the `cnt` bits shifted off the top;
`mpn_rshift` is the mirror. Each output limb is a funnel of two adjacent source
limbs. This module sources both kernels through the verified runtime-loop front:
the per-limb body is covered `LowCT` (`RArrLoad` / `RScalarSetExpr` over
`SShl` / `SShr` / `SAdd` / `SSub` / `RArrStore` at the runtime loop index), and
`Dialects.TranslateDialectRuntimeLoop.rolledForLoopNRt` front-compiles it
(`translateDialectControl` + `cryptoDialectToJasminCom`) and wraps it in a
`ComL.forLoopNRt` — one body copy behind a `jne` back-edge, the trip counter
seeded from the runtime `n` register.

```
  shiftBodyLowCT (RArrLoad rp/up at idx, SShl/SShr/SAdd funnel step,
                  RArrStore rp at idx and idx+1)
    --(rolledForLoopNRt)--> JLoopBodyN.update : Com jasminDialect [AR, reg 64, AU, reg 64] AR
    --(ComL.forLoopNRt update n rp [up, sh] (ret rp))--> ComL
    --(ComL.toLprogPhysAbi / renderLprogAtt)-----------> AT&T .s
```

## One body, two directions

Left and right shift are the same funnel with the two shift amounts exchanged.
The body takes a single scalar `sh` and derives `shb = 64 - sh`; the accumulator
holds the `2 ^ sh`-scaled value of the source across `n + 1` cells:

* `mpn_lshift` by `cnt` calls with `sh = cnt`. Cells `0, …, n-1` are the result
  limbs and cell `n` is the word shifted off the top.
* `mpn_rshift` by `cnt` calls with `sh = 64 - cnt`. Cell `0` is the word shifted
  off the bottom and cells `1, …, n` are the result limbs.

Both readings are instances of `shiftFold_val`.

## The carry cell

The loop-carried accumulator is the whole output array `rp`; the spilled bits of
the previous source limb ride in cell `idx` of that array. At trip `idx` the
body reads `rp[idx]` as the spill-in, adds it to `up[idx] << sh`, writes the
result to `rp[idx]`, and writes the new spill `up[idx] >> (64 - sh)` to
`rp[idx + 1]`. The spill-in occupies bits `[0, sh)` and the shifted limb bits
`[sh, 64)`, so the merge is a carry-free addition. The caller zeroes `rp[0]`.

`JLoopBodyN` carries one accumulator of a single `JasminTy` and `JasminTy` has
no product type, so a `(array, scalar)` pair cannot be loop-carried; routing the
spill through the output array is what keeps the body inside the covered
fragment. The alternative — reading `up[idx - 1]` directly — has no in-range
index at `idx = 0`, since `memGetDyn` reduces its index modulo the array width.

## ABI

```c
extern uint64_t *mpn_lshift_rt(uint64_t *rp, const uint64_t *up, uint64_t n, uint64_t sh);
extern uint64_t *mpn_rshift_rt(uint64_t *rp, const uint64_t *up, uint64_t n, uint64_t sh);
```

`rp` (RDI), `up` (RSI), `n` (RDX), `sh` (RCX). `rp` holds `n + 1` words. Both
symbols render the same `ComL`.

## Main results

* `shiftLimb_val`: the per-limb funnel identity
  `low + 2^64 · spill-out = a · 2^sh + spill-in`, for a spill-in below `2^sh`.
* `shiftLimb_spill_lt`: the spill-out is below `2^sh`, so the chain re-enters.
* `shiftFold_top_lt`: the accumulator cell at the trip index stays below `2^sh`.
* `shiftFold_val`: the loop invariant over the memref carrier — after `n` trips,
  `value (rp[0..n+1)) = value (up[0..n)) · 2^sh + rp[0]`, for every `NR`/`NU`.
* `lshiftFold_val`, `rshiftFold_val`: the two readings at spill-in zero.
* `shiftRtProg_denote`: the runtime-trip loop program's denotation as the fold.

## Scope

`shiftLimb_val`, `shiftFold_top_lt` and `shiftFold_val` hold for every `NR`/`NU`
and every `sh` with `0 < sh ≤ 64`; `NUS` fixes only the memref width of the
concrete front-compiled instance below, whose rendered SIB accesses are
byte-offset and so size-agnostic.

`shiftRtProg_denote` carries the front-compilation hypothesis
`frontLoopBodyJ … = some update` and concludes at `JLoopBodyN.denote` of that
`update`. Identifying that denotation with `shiftFoldStep` — so that
`shiftFold_val` reads as a statement about the emitted kernel — is the separate
source-preservation step (`translateDialectControl_denote_ctl` composed with
`cryptoDialectToJasminCom`), not established here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal bignumVal_snoc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (cells cells_succ cells_length memGetDyn_memSetDyn_ne memGetDyn_memSetDyn_self
   sv seqAll)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-! ## 1. Word facts for the funnel step -/

/-- `(w <<< r).toNat = (w.toNat * 2^r) % 2^64`. -/
theorem toNat_shiftLeft (w : BitVec 64) (r : Nat) :
    (w <<< r).toNat = w.toNat * 2 ^ r % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- A left-shifted limb has its low `r` bits zero (`r ≤ 64`). -/
theorem dvd_toNat_shiftLeft (w : BitVec 64) (r : Nat) (hr : r ≤ 64) :
    2 ^ r ∣ (w <<< r).toNat := by
  rw [toNat_shiftLeft, Nat.dvd_mod_iff (pow_dvd_pow 2 hr)]
  exact Dvd.intro_left _ rfl

/-- `(w >>> s).toNat = w.toNat / 2^s`. -/
theorem toNat_ushiftRight (w : BitVec 64) (s : Nat) :
    (w >>> s).toNat = w.toNat / 2 ^ s := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The spill word `w >>> (64 - r)` fits in `r` bits (`r ≤ 64`). -/
theorem toNat_spill_lt (w : BitVec 64) (r : Nat) (hr : r ≤ 64) :
    (w >>> (64 - r)).toNat < 2 ^ r := by
  rw [toNat_ushiftRight, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
    show r + (64 - r) = 64 from by omega]
  exact w.isLt

/-! ## 2. The per-limb funnel step -/

/-- One funnel limb step on words: shift the source limb `a` left by `sh`, add
    the spill-in `cy` (the bits that spilled out of the limb below), and split
    into `(output word, spill-out)`. The spill-out is the top `sh` bits of `a`. -/
def shiftLimb (sh : Nat) (a cy : BitVec 64) : BitVec 64 × BitVec 64 :=
  (a <<< sh + cy, a >>> (64 - sh))

/-- The spill-out fits in `sh` bits, so it is a legal spill-in for the next
    limb. -/
theorem shiftLimb_spill_lt (sh : Nat) (hsh : sh ≤ 64) (a cy : BitVec 64) :
    (shiftLimb sh a cy).2.toNat < 2 ^ sh :=
  toNat_spill_lt a sh hsh

/-- A left-shifted limb and a spill-in below `2 ^ sh` add without wrapping: the
    shifted limb's low `sh` bits are zero. -/
theorem shiftLimb_no_wrap (sh : Nat) (hsh : sh ≤ 64) (a cy : BitVec 64)
    (hcy : cy.toNat < 2 ^ sh) :
    (a <<< sh).toNat + cy.toNat < 2 ^ 64 := by
  obtain ⟨c, hc⟩ := dvd_toNat_shiftLeft a sh hsh
  have hlt : (a <<< sh).toNat < 2 ^ 64 := (a <<< sh).isLt
  have hsplit : (2 : ℕ) ^ 64 = 2 ^ sh * 2 ^ (64 - sh) := by
    rw [← pow_add]; congr 1; omega
  have hcpos : (0 : ℕ) < 2 ^ sh := Nat.two_pow_pos sh
  have hclt : c < 2 ^ (64 - sh) := by
    by_contra hcon
    have : 2 ^ sh * 2 ^ (64 - sh) ≤ 2 ^ sh * c :=
      Nat.mul_le_mul_left _ (Nat.le_of_not_lt hcon)
    omega
  have : 2 ^ sh * (c + 1) ≤ 2 ^ sh * 2 ^ (64 - sh) :=
    Nat.mul_le_mul_left _ (by omega)
  have hexp : 2 ^ sh * (c + 1) = 2 ^ sh * c + 2 ^ sh := by ring
  omega

/-- **The single-limb funnel identity.** `shiftLimb sh a cy` splits
    `a · 2^sh + cy` into an output word and a spill-out word:
    `output + 2^64 · spill-out = a · 2^sh + cy`. -/
theorem shiftLimb_val (sh : Nat) (hsh : sh ≤ 64) (a cy : BitVec 64)
    (hcy : cy.toNat < 2 ^ sh) :
    (shiftLimb sh a cy).1.toNat + 2 ^ 64 * (shiftLimb sh a cy).2.toNat
      = a.toNat * 2 ^ sh + cy.toNat := by
  have hnw := shiftLimb_no_wrap sh hsh a cy hcy
  have hadd : (a <<< sh + cy).toNat = (a <<< sh).toNat + cy.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hnw]
  have hsplit : (2 : ℕ) ^ 64 = 2 ^ sh * 2 ^ (64 - sh) := by
    rw [← pow_add]; congr 1; omega
  -- the high part of `a * 2^sh` is exactly the spill word
  have hdiv : a.toNat * 2 ^ sh / 2 ^ 64 = a.toNat / 2 ^ (64 - sh) := by
    rw [hsplit, Nat.mul_comm a.toNat (2 ^ sh),
      Nat.mul_div_mul_left _ _ (Nat.two_pow_pos sh)]
  have hdm : 2 ^ 64 * (a.toNat * 2 ^ sh / 2 ^ 64) + a.toNat * 2 ^ sh % 2 ^ 64
      = a.toNat * 2 ^ sh := Nat.div_add_mod _ _
  simp only [shiftLimb, hadd, toNat_shiftLeft, toNat_ushiftRight]
  rw [← hdiv]
  omega

/-! ## 3. The same chain over the memref carrier

The emitted loop carries the whole output array as its accumulator and folds one
body copy over the trip indices. `shiftFoldStep` is that body's word-level effect
and `shiftFold` the `(List.range n).foldl` shape `JLoopBodyN.denote` uses. -/

/-- One trip of the emitted loop on the accumulator array: read the spill-in from
    cell `t`, the source limb from `up[t]`, write the funnel's output word back
    to cell `t` and the spill-out to cell `t + 1`. -/
def shiftFoldStep {NR NUp : Nat} (up : Fin NUp → BitVec 64) (sh : Nat)
    (acc : Fin NR → BitVec 64) (t : Nat) : Fin NR → BitVec 64 :=
  memSetDyn (memSetDyn acc t (shiftLimb sh (memGetDyn up t) (memGetDyn acc t)).1)
    (t + 1) (shiftLimb sh (memGetDyn up t) (memGetDyn acc t)).2

/-- The `n`-fold of `shiftFoldStep` over the trip indices `0, …, n-1`: the
    `(List.range n).foldl` shape `JLoopBodyN.denote` folds the emitted loop body
    in, at accumulator type `.stackArr 64 NR`. -/
def shiftFold {NR NUp : Nat} (up : Fin NUp → BitVec 64) (sh : Nat)
    (n : Nat) (acc : Fin NR → BitVec 64) : Fin NR → BitVec 64 :=
  (List.range n).foldl (shiftFoldStep up sh) acc

/-- The fold peels its last trip. -/
theorem shiftFold_succ {NR NUp : Nat} (up : Fin NUp → BitVec 64) (sh : Nat)
    (n : Nat) (acc : Fin NR → BitVec 64) :
    shiftFold up sh (n + 1) acc = shiftFoldStep up sh (shiftFold up sh n acc) n := by
  simp [shiftFold, List.range_succ, List.foldl_append]

/-- Cells strictly below the trip index are already final: trip `t` writes only
    cells `t` and `t + 1`. -/
theorem shiftFoldStep_frame {NR NUp : Nat} (up : Fin NUp → BitVec 64) (sh : Nat)
    (acc : Fin NR → BitVec 64) (t j : Nat) (ht : t + 1 < NR) (hj : j < t) :
    memGetDyn (shiftFoldStep up sh acc t) j = memGetDyn acc j := by
  rw [shiftFoldStep,
    memGetDyn_memSetDyn_ne _ (t + 1) j _ ht (by omega) (by omega),
    memGetDyn_memSetDyn_ne _ t j _ (by omega) (by omega) (by omega)]

/-- The whole prefix below the trip index is unchanged. -/
theorem shiftFoldStep_cells {NR NUp : Nat} (up : Fin NUp → BitVec 64) (sh : Nat)
    (acc : Fin NR → BitVec 64) (t : Nat) (ht : t + 1 < NR) :
    cells (shiftFoldStep up sh acc t) t = cells acc t := by
  simp only [cells, List.map_inj_left, List.mem_range]
  intro j hj
  exact shiftFoldStep_frame up sh acc t j ht hj

/-- The accumulator cell at the trip index is a legal spill-in: it is the seeded
    cell `0` at the first trip and the previous trip's spill-out after that. -/
theorem shiftFold_top_lt {NR NUp : Nat} (up : Fin NUp → BitVec 64) (sh : Nat)
    (hsh : sh ≤ 64) (acc : Fin NR → BitVec 64) (h0 : (memGetDyn acc 0).toNat < 2 ^ sh) :
    ∀ n : Nat, n < NR → (memGetDyn (shiftFold up sh n acc) n).toNat < 2 ^ sh := by
  intro n
  cases n with
  | zero => intro _; simpa [shiftFold] using h0
  | succ k =>
      intro hkr
      rw [shiftFold_succ, shiftFoldStep,
        memGetDyn_memSetDyn_self _ (k + 1) _ hkr]
      exact shiftLimb_spill_lt sh hsh _ _

/-- **The funnel loop invariant.** After `n` trips the accumulator's first
    `n + 1` cells hold `up[0..n) · 2^sh` plus the seeded spill-in `acc[0]`. -/
theorem shiftFold_val {NR NUp : Nat} (up : Fin NUp → BitVec 64) (sh : Nat)
    (hsh : sh ≤ 64) (acc : Fin NR → BitVec 64)
    (h0 : (memGetDyn acc 0).toNat < 2 ^ sh) :
    ∀ n : Nat, n < NR →
      bignumVal (cells (shiftFold up sh n acc) (n + 1))
        = bignumVal (cells up n) * 2 ^ sh + (memGetDyn acc 0).toNat := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [shiftFold, cells, bignumVal]
  | succ k ih =>
      intro hkr
      have hkr' : k < NR := by omega
      set F : Fin NR → BitVec 64 := shiftFold up sh k acc with hF
      have hIH := ih hkr'
      have hcy : (memGetDyn F k).toNat < 2 ^ sh :=
        shiftFold_top_lt up sh hsh acc h0 k hkr'
      have hlow : memGetDyn (shiftFoldStep up sh F k) k
          = (shiftLimb sh (memGetDyn up k) (memGetDyn F k)).1 := by
        rw [shiftFoldStep,
          memGetDyn_memSetDyn_ne _ (k + 1) k _ hkr (by omega) (by omega),
          memGetDyn_memSetDyn_self _ k _ (by omega)]
      have hhigh : memGetDyn (shiftFoldStep up sh F k) (k + 1)
          = (shiftLimb sh (memGetDyn up k) (memGetDyn F k)).2 :=
        memGetDyn_memSetDyn_self _ (k + 1) _ hkr
      have hstep := shiftLimb_val sh hsh (memGetDyn up k) (memGetDyn F k) hcy
      have hkey : (shiftLimb sh (memGetDyn up k) (memGetDyn F k)).1.toNat * (2 ^ 64) ^ k
            + (shiftLimb sh (memGetDyn up k) (memGetDyn F k)).2.toNat
                * ((2 ^ 64) ^ k * 2 ^ 64)
          = (memGetDyn up k).toNat * 2 ^ sh * (2 ^ 64) ^ k
              + (memGetDyn F k).toNat * (2 ^ 64) ^ k := by
        calc (shiftLimb sh (memGetDyn up k) (memGetDyn F k)).1.toNat * (2 ^ 64) ^ k
              + (shiftLimb sh (memGetDyn up k) (memGetDyn F k)).2.toNat
                  * ((2 ^ 64) ^ k * 2 ^ 64)
            = ((shiftLimb sh (memGetDyn up k) (memGetDyn F k)).1.toNat
                + 2 ^ 64 * (shiftLimb sh (memGetDyn up k) (memGetDyn F k)).2.toNat)
              * (2 ^ 64) ^ k := by ring
          _ = ((memGetDyn up k).toNat * 2 ^ sh + (memGetDyn F k).toNat)
                * (2 ^ 64) ^ k := by rw [hstep]
          _ = (memGetDyn up k).toNat * 2 ^ sh * (2 ^ 64) ^ k
                + (memGetDyn F k).toNat * (2 ^ 64) ^ k := by ring
      rw [shiftFold_succ,
        cells_succ (shiftFoldStep up sh F k) (k + 1),
        cells_succ (shiftFoldStep up sh F k) k,
        bignumVal_snoc, bignumVal_snoc]
      simp only [List.length_append, List.length_cons, List.length_nil,
        cells_length, Nat.zero_add]
      rw [shiftFoldStep_cells up sh F k hkr, hlow, hhigh,
        cells_succ up k, bignumVal_snoc, cells_length,
        show ((2 : ℕ) ^ 64) ^ (k + 1) = (2 ^ 64) ^ k * 2 ^ 64 from pow_succ _ _]
      rw [cells_succ F k, bignumVal_snoc, cells_length] at hIH
      nlinarith [hIH, hkey]

/-- **`mpn_lshift` reading.** With `sh = cnt` and cell `0` seeded to zero, the
    accumulator's cells `0, …, n-1` are the shifted limbs and cell `n` is the
    word shifted off the top:
    `value (rp[0..n)) + rp[n] · 2^(64n) = value (up[0..n)) · 2^cnt`. -/
theorem lshiftFold_val {NR NUp : Nat} (up : Fin NUp → BitVec 64) (cnt : Nat)
    (hcnt : cnt ≤ 64) (acc : Fin NR → BitVec 64) (h0 : memGetDyn acc 0 = 0)
    (n : Nat) (hnr : n < NR) :
    bignumVal (cells (shiftFold up cnt n acc) (n + 1))
      = bignumVal (cells up n) * 2 ^ cnt := by
  have hz : (memGetDyn acc 0).toNat < 2 ^ cnt := by
    rw [h0]; simp
  rw [shiftFold_val up cnt hcnt acc hz n hnr, h0]
  simp

/-- **`mpn_rshift` reading.** With `sh = 64 - cnt` and cell `0` seeded to zero,
    the accumulator's cell `0` is the word shifted off the bottom and cells
    `1, …, n` are the shifted limbs:
    `value (rp[0..n+1)) · 2^cnt = value (up[0..n)) · 2^64`. -/
theorem rshiftFold_val {NR NUp : Nat} (up : Fin NUp → BitVec 64) (cnt : Nat)
    (hcnt : cnt ≤ 64) (acc : Fin NR → BitVec 64) (h0 : memGetDyn acc 0 = 0)
    (n : Nat) (hnr : n < NR) :
    bignumVal (cells (shiftFold up (64 - cnt) n acc) (n + 1)) * 2 ^ cnt
      = bignumVal (cells up n) * 2 ^ 64 := by
  rw [lshiftFold_val up (64 - cnt) (by omega) acc h0 n hnr, Nat.mul_assoc,
    ← pow_add, show 64 - cnt + cnt = 64 from by omega]

/-! ## 4. The loop body as covered `LowCT`

The body runs over the catCryptDialect context
`Γbody = [rp : .memref NRS, idx : .sword 64, up : .memref NUS, sh : .sword 64]` —
the accumulator array, the runtime loop index, then the two invariants. All
arithmetic is in the `srcClean` `SExpr` fragment (`SAdd`, `SSub`, `SShl`,
`SShr`), so `translateDialectControl` covers it. -/

/-- Limb count of the source array in the denotation model. The rendered SIB
    loads use byte offsets, so the assembly is size-agnostic; this only bounds
    the in-Lean model. The arithmetic results of §2 and §3 are stated for every
    `NUp` / `NR`. -/

abbrev NUS : Nat := 8

/-- Word count of the output array: `NUS` result words plus the spill cell. -/
abbrev NRS : Nat := NUS + 1

/-- The output-array slot `rp` (`NRS` words), the loop accumulator. -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * NRS)⟩

/-- The source-array slot `up` (`NUS` words), a loop invariant. -/
def upLoc : Located := ⟨"up", .TBytes (8 * NUS)⟩

/-- One funnel limb at the runtime loop index `idx`: read the spill-in from
    `rp[idx]` and the source limb from `up[idx]`, derive the complementary shift
    amount `64 - sh`, form the shifted limb and the spill-out, add the spill-in
    into the shifted limb, then store the output word to `rp[idx]` and the
    spill-out to `rp[idx + 1]`. -/
def shiftBodyLowCT : LowCT := seqAll
  [ .RArrLoad ⟨"cy", .TU64⟩ rpLoc "idx"
  , .RArrLoad ⟨"t", .TU64⟩ upLoc "idx"
  , .RScalarSetExpr "shb" (.SSub (.SLit 64) (sv "sh"))
  , .RScalarSetExpr "lo" (.SShl (sv "t") (sv "sh"))
  , .RScalarSetExpr "hi" (.SShr (sv "t") (sv "shb"))
  , .RScalarSetExpr "s" (.SAdd (sv "lo") (sv "cy"))
  , .RArrStore rpLoc "idx" ⟨"s", .TU64⟩
  , .RScalarSetExpr "idx1" (.SAdd (sv "idx") (.SLit 1))
  , .RArrStore rpLoc "idx1" ⟨"hi", .TU64⟩ ]

/-- The loop-body context: accumulator `rp`, runtime loop index, then the source
    array `up` and the scalar shift amount `sh` as invariants. -/
def Gbody : Ctx := [.memref NRS, .sword 64, .memref NUS, .sword 64]

/-- The body `VarMap`: `sh` bound deepest, then `up`, then `idx`, then `rp` at
    `.here`. -/
def vmBody : VarMap Gbody :=
  ((((VarMap.empty.bind (t := .sword 64) "sh").bind
      (t := .memref NUS) "up").bind
      (t := .sword 64) "idx").bind (t := .memref NRS) "rp")

/-! ## 5. The runtime-trip loop program

Outer argument context `[sh, n, up, rp]` (newest first), routing
`rp → RDI`, `up → RSI`, `n → RDX`, `sh → RCX`. -/

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The output-array jasmin type. -/
abbrev AR : JasminTy := .stackArr 64 NRS

/-- The source-array jasmin type. -/
abbrev AU : JasminTy := .stackArr 64 NUS

/-- The kernel's outer argument context, newest first. -/
abbrev Gouter : Ctxt jasminDialect := [r64, r64, AU, AR]

/-- The runtime trip count `n` (RDX). -/
def shiftCount : Ctxt.Var Gouter r64 := .there .here

/-- The accumulator seed: the output array `rp` (RDI). -/
def shiftInit : Ctxt.Var Gouter AR := .there (.there (.there .here))

/-- The loop invariants: the source array `up` (RSI) and the scalar shift amount
    `sh` (RCX). The array leads the list so that the export's positional
    invariant-to-ABI-register zip (`ComL.loopArgBaseNames` feeding
    `ComL.toLfundefPhysAbi`'s reload map, which does not filter scalars out of
    the invariant list) pairs `up` with `RSI`. -/
def shiftInvs : HVector (fun ty => Ctxt.Var Gouter ty) [AU, r64] :=
  .cons (.there (.there .here)) (.cons .here .nil)

/-- The front-compiled runtime-trip funnel shift: one body copy behind a `jne`
    back-edge, the trip counter seeded from the runtime `n` register, the output
    array threaded as the loop accumulator and `up`/`sh` as loop invariants.
    `none` if the front declines. -/
def shiftRtProgOpt : Option (ComL Gouter AR) :=
  rolledForLoopNRt (Γouter := Gouter) (accCTy := .memref NRS)
    (invCTys := [.memref NUS, .sword 64])
    vmBody "rp" shiftBodyLowCT shiftCount shiftInit shiftInvs

-- The front accepts the body and wraps it in a `ComL.forLoopNRt`.
#guard shiftRtProgOpt.isSome

/-- **The emitted loop's denotation is the `JLoopBodyN` fold of the front body.**
    Whenever the front compiles `shiftBodyLowCT` to `update`, the runtime-trip
    program's denotation at any valuation is the `n`-fold of `update` over the
    trip indices, seeded by the `rp` argument and threading `up` and `sh`. The
    instance of `rolledForLoopNRt_denote` at this kernel. -/
theorem shiftRtProg_denote
    {update : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.memref NRS :: .sword 64 ::
        [CryptoTy.memref NUS, CryptoTy.sword 64]))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NRS))}
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJ
      (accCTy := .memref NRS) vmBody "rp" shiftBodyLowCT = some update)
    (V : Ctxt.Valuation Gouter) :
    shiftRtProgOpt.map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(shiftCount.lookup V).toNat, update⟩
          (Expr.lookupArgs shiftInvs V) (shiftInit.lookup V)) :=
  rolledForLoopNRt_denote vmBody "rp" shiftBodyLowCT shiftCount shiftInit shiftInvs
    hupd V

/-! ## 6. The owned `Lprog` and the rendered `.s` -/

/-- The rolled, owned-RA 4-argument-ABI `Lprog` for the runtime-trip funnel
    shift under the C symbol `fname`
    (`RDI = rp`, `RSI = up`, `RDX = n`, `RCX = sh`). -/
def shiftRtLprogOpt (fname : String) : Option Lprog :=
  shiftRtProgOpt.map (fun c =>
    ComL.toLprogPhysAbi c fname (argName 0) [argName 1]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64])

/-- The owned AT&T `.s` text for the runtime-trip funnel shift. -/
def shiftRtAsmOpt (fname : String) : Option String :=
  (shiftRtLprogOpt fname).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

/-- The `mpn_lshift` symbol: the funnel kernel called with `sh = cnt`. -/
def lshiftRtAsmOpt : Option String := shiftRtAsmOpt "mpn_lshift_rt"

/-- The `mpn_rshift` symbol: the funnel kernel called with `sh = 64 - cnt`. -/
def rshiftRtAsmOpt : Option String := shiftRtAsmOpt "mpn_rshift_rt"

/-- The 4-argument-ABI physical body of the front-compiled runtime-count loop. -/
def shiftRtPhysBodyOpt : Option Lcmd :=
  shiftRtProgOpt.map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX"]
      [64, 64, 64, 64]).lfd_body)

-- The physical body carries a real back-edge: an internal label and a
-- conditional jump, so the emit is a counted loop and not an unrolled chain.
#guard (shiftRtPhysBodyOpt.map (fun body =>
  (body.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
    && (body.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false))))
  = some true

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would
-- re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 7. Emit driver

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency.

`lshiftRtAsmOpt` and `rshiftRtAsmOpt` are the same rendered body under two
symbol names, so one file is written, under the direction-neutral symbol
`mpn_shift_rt`. The caller picks the direction with `sh`: `sh = cnt` is
`mpn_lshift`, `sh = 64 - cnt` is `mpn_rshift`. -/

/-- Write the owned-backend `.s` for the runtime-trip funnel shift into the
    `bench/mpn_shift_front_compare/gen_com` harness directory. -/
def emitMain : IO Unit := do
  let dir := "bench/mpn_shift_front_compare/gen_com"
  IO.FS.createDirAll dir
  match shiftRtAsmOpt "mpn_shift_rt" with
  | some s =>
      IO.FS.writeFile (dir ++ "/mpn_shift_rt_owned.s") s
      IO.println "WROTE bench/mpn_shift_front_compare/gen_com/mpn_shift_rt_owned.s"
  | none => throw (IO.userError "the runtime-loop front declined the funnel shift")

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit
