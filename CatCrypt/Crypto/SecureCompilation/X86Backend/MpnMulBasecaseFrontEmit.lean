/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# `mpn_mul_basecase` as a front-generated nested runtime-trip loop

`mpn_mul_basecase(rp, up, un, vp, vn)` sets `rp[0..un+vn) = up[0..un) *
vp[0..vn)` by schoolbook multiplication. This module sources that kernel through
the verified nested runtime-loop front: the per-limb body is covered `LowCT`
(`RArrLoad` / `RScalarSetExpr` / `RArrStore` over the two runtime loop indices),
and the rolled-loop dispatcher's nested route
(`Dialects.FrontRoutePlan.compileNested` at the `plain` body front, which is the
front the two bodies are stated over) front-compiles
it together with an inner-trip-count body and wraps them in a
`ComL.forLoopNRtNested` — two body copies behind two `jne` back-edges, the outer
trip counter seeded from the runtime `vn` register and the inner trip recomputed
from the loop-invariant `un` each outer pass.

```
  rowBodyLowCT (RArrLoad rp/up/vp at runtime indices, SMul/SMulHiU/SAdd/bSltu
                carry step, RArrStore rp at two indices)
    --(compileNested .plain)----> ComL.forLoopNRtNested
    --(ComL.toLprogPhysAbi / renderLprogAtt)-----------> AT&T .s
```

## The carry cell

`JLoopBodyN` carries ONE accumulator of ONE `JasminTy`, so the output array, the
running carry and the two input arrays cannot each be a separate loop-carried
value. The loop-carried accumulator is the output array `rp`; the running
addmul carry rides in the scratch word `rp[un + vn]`, one past the `un + vn`
product words. `up` and `vp` are loop invariants (read every trip, never
written), and the row index is the outer loop binder.

## The flush trip

The inner loop runs `un + 1` trips per row. Trips `0, …, un-1` are the
`mpn_addmul_1` steps `rp[jd+t] += up[t] * vp[jd] + carry`; trip `un` writes the
row's final carry to `rp[jd+un]`. The two are the same body: at `t = un` the
branch-free mask `0 - bSltu t un` is zero, so the multiplicand limb reads as `0`
and the step degenerates to `rp[jd+un] := carry`, `carry := 0`. The mask also
clamps the `up` index, so trip `un` reads `up[0]` rather than one word past the
array.

## ABI

```c
extern uint64_t *mpn_mul_basecase_rt(uint64_t *rp, const uint64_t *up,
                                     const uint64_t *vp, uint64_t un, uint64_t vn);
```

`rp` (RDI), `up` (RSI), `vp` (RDX), `un` (RCX), `vn` (R8). `rp` holds
`un + vn + 1` words, zeroed on entry; on return `rp[0..un+vn)` is the product
and `rp[un+vn]` is `0`.

## Main results

* `mulAddLimb` / `mulAddLimb_val`: the per-limb word step
  `low + 2^64 · carry-out = a · v + cy + r` of one `addmul_1` position.
* `bcSel_eq`: the branch-free mask select reads `up[t]` for `t < un` and `0` at
  the flush trip.
* `bignumVal_cells_setDyn`: the single-cell framing lemma for `bignumVal` over a
  memref prefix.
* `bcStep_val`: one inner trip's effect on
  `value(rp[0..nc)) + 2^(64(jd+t)) · carry`.
* `bcRow_val`: one schoolbook row adds `2^(64·jd) · value(up) · vp[jd]` and
  leaves the carry cell zero.
* `bcFold_val`: the accumulated invariant
  `value(rp[0..un+vn)) = value(up[0..un)) · value(vp[0..vn))`, by induction over
  rows.
* `bcFold_val_sqr`: the squaring specialisation at `vp := up`, `vn := un`.
* `bcProgOpt` / `bcProg_denote`: the front-compiled nested runtime-trip program
  and its denotation as the `JLoopBodyN.nestedDenote` double fold.
* `bcRtLprogOpt` / `bcRtAsmOpt`: the owned `Lprog` and the rendered AT&T `.s`.

## Scope

`mulAddLimb_val`, `bcStep_val`, `bcRow_val` and `bcFold_val` hold for every
`NR` / `NU` / `NV` and every runtime `un` / `vn` / `nc`; the concrete
front-compiled instance below fixes only the memref widths of the denotation
model, and the rendered SIB accesses are byte-offset and so size-agnostic.

`bcProg_denote` carries the two front-compilation hypotheses and concludes at
`JLoopBodyN.nestedDenote` of the front bodies. Identifying that denotation with
`bcStep` — so that `bcFold_val` reads as a statement about the emitted kernel —
is the separate source-preservation step (`translateDialectControl_denote_ctl`
composed with `cryptoDialectToJasminCom`), not established here: the arithmetic
of §1–§3 is about the word-level model, not about the emitted body.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit

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
   addCarry_split bSltu_le_one seqAll ltuCmds sv)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-! ## 1. The per-position word step -/

/-- One `mpn_addmul_1` position on words: multiply the limb `a` by the row
    scalar `v`, add the running carry `cy` and the destination word `r`, and
    split into `(low word, carry-out)`. Both carry-out bits are the branch-free
    `bSltu` of a sum against its first summand. -/
def mulAddLimb (a v cy r : BitVec 64) : BitVec 64 × BitVec 64 :=
  let lo := a * v
  let s1 := lo + cy
  let s2 := s1 + r
  (s2, mulHiW a v + bSltu s1 lo + bSltu s2 s1)

/-- **The single-position addmul identity.** `mulAddLimb a v cy r` splits
    `a · v + cy + r` into a low word and a carry-out word:
    `low + 2 ^ 64 · carry-out = a · v + cy + r`. -/
theorem mulAddLimb_val (a v cy r : BitVec 64) :
    (mulAddLimb a v cy r).1.toNat + 2 ^ 64 * (mulAddLimb a v cy r).2.toNat
      = a.toNat * v.toNat + cy.toNat + r.toNat := by
  have hab := mulx_reconstruct a v
  have h1 := addCarry_split (a * v) cy
  have h2 := addCarry_split (a * v + cy) r
  have hc1 := bSltu_le_one (a * v + cy) (a * v)
  have hc2 := bSltu_le_one (a * v + cy + r) (a * v + cy)
  have hhi := mulHiW_le a v
  have hlo := (a * v).isLt
  have hs1 := (a * v + cy).isLt
  have hs2 := (a * v + cy + r).isLt
  have hcy := cy.isLt
  have hr := r.isLt
  -- The true high word `hi + c1 + c2` is `< 2 ^ 64`, so neither addition wraps.
  have hsum : (mulHiW a v).toNat + (bSltu (a * v + cy) (a * v)).toNat
      + (bSltu (a * v + cy + r) (a * v + cy)).toNat < 2 ^ 64 := by
    have hprod : a.toNat * v.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by have := a.isLt; omega) (by have := v.isLt; omega)
    obtain ⟨P, hP⟩ : ∃ P, a.toNat * v.toNat = P := ⟨_, rfl⟩
    rw [hP] at hab hprod
    norm_num at hprod
    omega
  have hno1 : (mulHiW a v + bSltu (a * v + cy) (a * v)).toNat
      = (mulHiW a v).toNat + (bSltu (a * v + cy) (a * v)).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hno2 : (mulHiW a v + bSltu (a * v + cy) (a * v)
        + bSltu (a * v + cy + r) (a * v + cy)).toNat
      = (mulHiW a v).toNat + (bSltu (a * v + cy) (a * v)).toNat
        + (bSltu (a * v + cy + r) (a * v + cy)).toNat := by
    rw [BitVec.toNat_add, hno1, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨P, hP⟩ : ∃ P, a.toNat * v.toNat = P := ⟨_, rfl⟩
  rw [hP] at hab ⊢
  simp only [mulAddLimb, hno2]
  omega

/-- At the flush trip the multiplicand limb is `0` and the destination word is
    `0`, so the step moves the carry into place and clears it. -/
theorem mulAddLimb_flush (v cy : BitVec 64) :
    mulAddLimb 0 v cy 0 = (cy, 0) := by
  have hzero : ((0 : BitVec 64)).toNat = 0 := rfl
  have hval := mulAddLimb_val 0 v cy 0
  simp only [hzero, Nat.zero_mul, Nat.zero_add, Nat.add_zero] at hval
  have hlt := (mulAddLimb 0 v cy 0).1.isLt
  have hcy := cy.isLt
  have h2 : (mulAddLimb 0 v cy 0).2.toNat = 0 := by omega
  have h1 : (mulAddLimb 0 v cy 0).1.toNat = cy.toNat := by omega
  refine Prod.ext ?_ ?_
  · exact BitVec.eq_of_toNat_eq h1
  · exact BitVec.eq_of_toNat_eq (by rw [h2, hzero])

/-! ## 2. The branch-free flush-trip mask -/

/-- The multiplicand limb read at inner trip `t` of a row: the mask
    `0 - bSltu t un` is all-ones while `t < un` and zero at the flush trip
    `t = un`, and it clamps both the array index and the loaded word. -/
def bcSel {NU : Nat} (up : Fin NU → BitVec 64) (un t : BitVec 64) : BitVec 64 :=
  memGetDyn up (t &&& (0 - bSltu t un)).toNat &&& (0 - bSltu t un)

/-- **The mask select reads `up[t]` below the flush trip and `0` at it.** -/
theorem bcSel_eq {NU : Nat} (up : Fin NU → BitVec 64) (un t : BitVec 64) :
    bcSel up un t = if t.toNat < un.toNat then memGetDyn up t.toNat else 0 := by
  have hones : (0 : BitVec 64) - 1 = BitVec.allOnes 64 := by decide
  simp only [bcSel, bSltu_eq, BitVec.ult]
  by_cases h : t.toNat < un.toNat
  · simp only [h, decide_true, if_pos, hones, BitVec.and_allOnes]
  · simp [h]

/-! ## 3. The schoolbook fold over the memref carrier

The emitted nest carries the whole output array as its accumulator and folds one
inner body copy over the inner trip indices, once per outer row. `bcStep` is the
inner body's word-level effect and `bcRow` / `bcFold` the `(List.range _).foldl`
shapes `JLoopBodyN.nestedDenote` uses. -/

/-- The multiplicand limb at inner trip `t`: `up[t]` below the flush trip, `0`
    at it. -/
def bcLimb {NU : Nat} (up : Fin NU → BitVec 64) (un t : Nat) : BitVec 64 :=
  if t < un then memGetDyn up t else 0

/-- One inner trip of the emitted nest at row `jd`, inner index `t`: read the
    running carry from the scratch cell `nc`, the multiplicand limb from `up`,
    the row scalar from `vp[jd]` and the destination word from `rp[jd+t]`; write
    the low word back to `rp[jd+t]` and the carry-out to the scratch cell. -/
def bcStep {NR NU NV : Nat} (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64)
    (un nc jd : Nat) (acc : Fin NR → BitVec 64) (t : Nat) : Fin NR → BitVec 64 :=
  memSetDyn
    (memSetDyn acc (jd + t)
      (mulAddLimb (bcLimb up un t) (memGetDyn vp jd) (memGetDyn acc nc)
        (memGetDyn acc (jd + t))).1)
    nc
    (mulAddLimb (bcLimb up un t) (memGetDyn vp jd) (memGetDyn acc nc)
      (memGetDyn acc (jd + t))).2

/-- The first `T` inner trips of row `jd`. -/
def bcPartial {NR NU NV : Nat} (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64)
    (un nc jd : Nat) (acc : Fin NR → BitVec 64) (T : Nat) : Fin NR → BitVec 64 :=
  (List.range T).foldl (bcStep up vp un nc jd) acc

/-- One whole schoolbook row: `un` addmul trips followed by the flush trip. -/
def bcRow {NR NU NV : Nat} (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64)
    (un nc jd : Nat) (acc : Fin NR → BitVec 64) : Fin NR → BitVec 64 :=
  bcPartial up vp un nc jd acc (un + 1)

/-- The outer fold over `n` rows: the `JLoopBodyN.nestedDenote` shape at
    constant inner trip `un + 1`. -/
def bcFold {NR NU NV : Nat} (up : Fin NU → BitVec 64) (vp : Fin NV → BitVec 64)
    (un nc : Nat) (n : Nat) (acc : Fin NR → BitVec 64) : Fin NR → BitVec 64 :=
  (List.range n).foldl (fun a jd => bcRow up vp un nc jd a) acc

/-- The partial row fold peels its last trip. -/
theorem bcPartial_succ {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc jd : Nat) (acc : Fin NR → BitVec 64) (T : Nat) :
    bcPartial up vp un nc jd acc (T + 1)
      = bcStep up vp un nc jd (bcPartial up vp un nc jd acc T) T := by
  simp [bcPartial, List.range_succ, List.foldl_append]

/-- The outer fold peels its last row. -/
theorem bcFold_succ {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc n : Nat) (acc : Fin NR → BitVec 64) :
    bcFold up vp un nc (n + 1) acc = bcRow up vp un nc n (bcFold up vp un nc n acc) := by
  simp [bcFold, List.range_succ, List.foldl_append]

/-! ### Framing -/

/-- A cell other than the two the trip writes is unchanged. -/
theorem bcStep_frame {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc jd : Nat) (acc : Fin NR → BitVec 64) (t i : Nat)
    (hnc : nc < NR) (hin : i < nc) (hjt : jd + t < nc) (hne : i ≠ jd + t) :
    memGetDyn (bcStep up vp un nc jd acc t) i = memGetDyn acc i := by
  rw [bcStep,
    memGetDyn_memSetDyn_ne _ nc i _ hnc (by omega) (by omega),
    memGetDyn_memSetDyn_ne _ (jd + t) i _ (by omega) (by omega) hne]

/-- A cell the row never writes is unchanged across any prefix of the row. -/
theorem bcPartial_frame {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc jd : Nat) (acc : Fin NR → BitVec 64) (i : Nat)
    (hnc : nc < NR) (hin : i < nc) :
    ∀ T : Nat, (∀ t, t < T → jd + t < nc ∧ i ≠ jd + t) →
      memGetDyn (bcPartial up vp un nc jd acc T) i = memGetDyn acc i := by
  intro T
  induction T with
  | zero => intro _; rfl
  | succ k ih =>
      intro hT
      rw [bcPartial_succ,
        bcStep_frame up vp un nc jd _ k i hnc hin (hT k (by omega)).1
          (hT k (by omega)).2,
        ih (fun t ht => hT t (by omega))]

/-- The scratch cell after a trip is the trip's carry-out. -/
theorem bcStep_carry {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc jd : Nat) (acc : Fin NR → BitVec 64) (t : Nat)
    (hnc : nc < NR) :
    memGetDyn (bcStep up vp un nc jd acc t) nc
      = (mulAddLimb (bcLimb up un t) (memGetDyn vp jd) (memGetDyn acc nc)
          (memGetDyn acc (jd + t))).2 :=
  memGetDyn_memSetDyn_self _ nc _ hnc

/-- The destination cell after a trip is the trip's low word. -/
theorem bcStep_low {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc jd : Nat) (acc : Fin NR → BitVec 64) (t : Nat)
    (hnc : nc < NR) (hjt : jd + t < nc) :
    memGetDyn (bcStep up vp un nc jd acc t) (jd + t)
      = (mulAddLimb (bcLimb up un t) (memGetDyn vp jd) (memGetDyn acc nc)
          (memGetDyn acc (jd + t))).1 := by
  rw [bcStep,
    memGetDyn_memSetDyn_ne _ nc (jd + t) _ hnc (by omega) (by omega),
    memGetDyn_memSetDyn_self _ (jd + t) _ (by omega)]

/-! ### The `bignumVal` framing lemma -/

/-- Cells strictly below `K` are unchanged by a write at an index `≥ K`. -/
theorem cells_setDyn_of_le {N : Nat} (acc : Fin N → BitVec 64) (K k : Nat)
    (w : BitVec 64) (hkK : K ≤ k) (hk : k < N) :
    cells (memSetDyn acc k w) K = cells acc K := by
  simp only [cells, List.map_inj_left, List.mem_range]
  intro j hj
  exact memGetDyn_memSetDyn_ne acc k j w hk (by omega) (by omega)

/-- **Single-cell framing for `bignumVal`.** Rewriting cell `k` of a memref
    prefix of length `K` replaces that cell's weighted contribution. -/
theorem bignumVal_cells_setDyn {N : Nat} (acc : Fin N → BitVec 64) (K k : Nat)
    (w : BitVec 64) (hk : k < K) (hKN : K ≤ N) :
    bignumVal (cells (memSetDyn acc k w) K) + (2 ^ 64) ^ k * (memGetDyn acc k).toNat
      = bignumVal (cells acc K) + (2 ^ 64) ^ k * w.toNat := by
  induction K with
  | zero => exact absurd hk (by omega)
  | succ m ih =>
      rw [cells_succ, cells_succ, bignumVal_snoc, bignumVal_snoc, cells_length,
        cells_length]
      rcases Nat.lt_or_ge k m with hkm | hkm
      · have hmn : m < N := by omega
        rw [memGetDyn_memSetDyn_ne acc k m w (by omega) hmn (by omega)]
        have hih := ih hkm (by omega)
        linarith
      · have hkm' : k = m := by omega
        subst hkm'
        rw [cells_setDyn_of_le acc k k w (by omega) (by omega),
          memGetDyn_memSetDyn_self acc k w (by omega)]
        ring

/-- The `bignumVal` of an all-zero prefix is zero. -/
theorem bignumVal_cells_zero {N : Nat} (acc : Fin N → BitVec 64) (K : Nat)
    (hz : ∀ i, i < K → memGetDyn acc i = 0) : bignumVal (cells acc K) = 0 := by
  induction K with
  | zero => simp [cells, bignumVal]
  | succ m ih =>
      rw [cells_succ, bignumVal_snoc, ih (fun i hi => hz i (by omega)),
        hz m (by omega)]
      simp

/-! ### The per-trip and per-row value identities -/

/-- **One inner trip's value identity.** The trip moves
    `2 ^ (64(jd+t)) · (a · v)` into the accumulated product region, re-weighting
    the running carry from `2 ^ (64(jd+t))` to `2 ^ (64(jd+t+1))`. -/
theorem bcStep_val {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc jd t : Nat) (acc : Fin NR → BitVec 64)
    (hnc : nc < NR) (hjt : jd + t < nc) :
    bignumVal (cells (bcStep up vp un nc jd acc t) nc)
        + (2 ^ 64) ^ (jd + t + 1)
            * (memGetDyn (bcStep up vp un nc jd acc t) nc).toNat
      = bignumVal (cells acc nc) + (2 ^ 64) ^ (jd + t) * (memGetDyn acc nc).toNat
        + (2 ^ 64) ^ (jd + t)
            * ((bcLimb up un t).toNat * (memGetDyn vp jd).toNat) := by
  set w := mulAddLimb (bcLimb up un t) (memGetDyn vp jd) (memGetDyn acc nc)
    (memGetDyn acc (jd + t)) with hw
  have hval : w.1.toNat + 2 ^ 64 * w.2.toNat
      = (bcLimb up un t).toNat * (memGetDyn vp jd).toNat
        + (memGetDyn acc nc).toNat + (memGetDyn acc (jd + t)).toNat :=
    mulAddLimb_val _ _ _ _
  have hcarry : memGetDyn (bcStep up vp un nc jd acc t) nc = w.2 :=
    bcStep_carry up vp un nc jd acc t hnc
  have hcells : cells (bcStep up vp un nc jd acc t) nc
      = cells (memSetDyn acc (jd + t) w.1) nc :=
    cells_setDyn_of_le _ nc nc w.2 (by omega) hnc
  have hframe := bignumVal_cells_setDyn acc nc (jd + t) w.1 hjt (by omega)
  have hpow : (2 ^ 64 : Nat) ^ (jd + t + 1) = (2 ^ 64) ^ (jd + t) * 2 ^ 64 :=
    pow_succ _ _
  rw [hcarry, hcells, hpow]
  -- Scale the word identity by the position weight and cancel the destination word.
  have hscaled : (2 ^ 64 : Nat) ^ (jd + t) * w.1.toNat
        + (2 ^ 64) ^ (jd + t) * (2 ^ 64 * w.2.toNat)
      = (2 ^ 64) ^ (jd + t)
          * ((bcLimb up un t).toNat * (memGetDyn vp jd).toNat)
        + (2 ^ 64) ^ (jd + t) * (memGetDyn acc nc).toNat
        + (2 ^ 64) ^ (jd + t) * (memGetDyn acc (jd + t)).toNat := by
    rw [← Nat.mul_add, hval]; ring
  have hassoc : (2 ^ 64 : Nat) ^ (jd + t) * 2 ^ 64 * w.2.toNat
      = (2 ^ 64) ^ (jd + t) * (2 ^ 64 * w.2.toNat) := by ring
  rw [hassoc]
  omega

/-- **The row-prefix invariant.** After `T ≤ un` addmul trips of row `jd`, the
    product region plus the weighted running carry has absorbed
    `2 ^ (64·jd) · value(up[0..T)) · vp[jd]`. -/
theorem bcPartial_val {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc jd : Nat) (acc : Fin NR → BitVec 64)
    (hnc : nc < NR) (hjd : jd + un < nc) :
    ∀ T : Nat, T ≤ un →
      bignumVal (cells (bcPartial up vp un nc jd acc T) nc)
          + (2 ^ 64) ^ (jd + T)
              * (memGetDyn (bcPartial up vp un nc jd acc T) nc).toNat
        = bignumVal (cells acc nc) + (2 ^ 64) ^ jd * (memGetDyn acc nc).toNat
          + (2 ^ 64) ^ jd
              * (bignumVal (cells up T) * (memGetDyn vp jd).toNat) := by
  intro T
  induction T with
  | zero => intro _; simp [bcPartial, cells, bignumVal]
  | succ k ih =>
      intro hk
      have hkun : k < un := by omega
      have hstep := bcStep_val up vp un nc jd k
        (bcPartial up vp un nc jd acc k) hnc (by omega)
      have hIH := ih (by omega)
      have hlimb : bcLimb up un k = memGetDyn up k := by
        simp [bcLimb, hkun]
      rw [hlimb] at hstep
      have hupsucc : bignumVal (cells up (k + 1))
          = bignumVal (cells up k) + (memGetDyn up k).toNat * (2 ^ 64) ^ k := by
        rw [cells_succ, bignumVal_snoc, cells_length]
      have hexpand : (2 ^ 64 : Nat) ^ jd
            * ((bignumVal (cells up k) + (memGetDyn up k).toNat * (2 ^ 64) ^ k)
                * (memGetDyn vp jd).toNat)
          = (2 ^ 64) ^ jd * (bignumVal (cells up k) * (memGetDyn vp jd).toNat)
            + (2 ^ 64) ^ (jd + k)
                * ((memGetDyn up k).toNat * (memGetDyn vp jd).toNat) := by
        rw [pow_add]; ring
      rw [bcPartial_succ, show jd + (k + 1) = jd + k + 1 from rfl, hupsucc, hexpand]
      linarith

/-! ### One whole row -/

/-- **One schoolbook row.** Given a clean carry cell and a zero destination word
    above the row's addmul range, the row adds
    `2 ^ (64·jd) · value(up[0..un)) · vp[jd]` to the product region and leaves
    the carry cell zero. -/
theorem bcRow_val {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc jd : Nat) (acc : Fin NR → BitVec 64)
    (hnc : nc < NR) (hjd : jd + un < nc)
    (hcy : memGetDyn acc nc = 0) (htop : memGetDyn acc (jd + un) = 0) :
    bignumVal (cells (bcRow up vp un nc jd acc) nc)
        = bignumVal (cells acc nc)
          + (2 ^ 64) ^ jd * (bignumVal (cells up un) * (memGetDyn vp jd).toNat)
      ∧ memGetDyn (bcRow up vp un nc jd acc) nc = 0 := by
  have hzero : ((0 : BitVec 64)).toNat = 0 := rfl
  have hA := bcPartial_val up vp un nc jd acc hnc hjd un (by omega)
  -- The addmul prefix never touches the destination word of the flush trip.
  have htopA : memGetDyn (bcPartial up vp un nc jd acc un) (jd + un) = 0 := by
    rw [bcPartial_frame up vp un nc jd acc (jd + un) hnc (by omega) un
      (fun t ht => ⟨by omega, by omega⟩)]
    exact htop
  have hlimb : bcLimb up un un = 0 := by simp [bcLimb]
  have hstep := bcStep_val up vp un nc jd un
    (bcPartial up vp un nc jd acc un) hnc (by omega)
  have hcarry := bcStep_carry up vp un nc jd (bcPartial up vp un nc jd acc un) un hnc
  rw [hlimb, htopA, mulAddLimb_flush] at hcarry
  have hcarry0 : memGetDyn (bcStep up vp un nc jd
      (bcPartial up vp un nc jd acc un) un) nc = 0 := hcarry
  rw [hlimb, hcarry0] at hstep
  simp only [hzero, Nat.zero_mul, Nat.mul_zero, Nat.add_zero] at hstep
  rw [hcy] at hA
  simp only [hzero, Nat.mul_zero, Nat.add_zero] at hA
  have hrow : bcRow up vp un nc jd acc
      = bcStep up vp un nc jd (bcPartial up vp un nc jd acc un) un := by
    rw [bcRow, bcPartial_succ]
  exact ⟨by rw [hrow]; linarith, by rw [hrow]; exact hcarry0⟩

/-- The row never writes a cell above its top destination word. -/
theorem bcRow_frame_gt {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc jd : Nat) (acc : Fin NR → BitVec 64) (i : Nat)
    (hnc : nc < NR) (hin : i < nc) (hi : jd + un < i) :
    memGetDyn (bcRow up vp un nc jd acc) i = memGetDyn acc i :=
  bcPartial_frame up vp un nc jd acc i hnc hin (un + 1)
    (fun t ht => ⟨by omega, by omega⟩)

/-! ### The accumulated invariant -/

/-- Cells `m, …, nc-1` of the accumulator are zero. -/
def ZeroFrom {NR : Nat} (acc : Fin NR → BitVec 64) (m nc : Nat) : Prop :=
  ∀ i, m ≤ i → i < nc → memGetDyn acc i = 0

/-- **The schoolbook loop invariant.** After `n` rows the product region holds
    the accumulated product `value(up[0..un)) · value(vp[0..n))`, the carry cell
    is zero, and the cells above the written range are still zero. -/
theorem bcFold_val {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un nc : Nat) (acc : Fin NR → BitVec 64)
    (hnc : nc < NR) (hcy : memGetDyn acc nc = 0) :
    ∀ n : Nat, n + un ≤ nc → ZeroFrom acc un nc →
      bignumVal (cells (bcFold up vp un nc n acc) nc)
          = bignumVal (cells acc nc)
            + bignumVal (cells up un) * bignumVal (cells vp n)
        ∧ memGetDyn (bcFold up vp un nc n acc) nc = 0
        ∧ ZeroFrom (bcFold up vp un nc n acc) (n + un) nc := by
  intro n
  induction n with
  | zero =>
      intro _ hz
      refine ⟨by simp [bcFold, cells, bignumVal], by simpa [bcFold] using hcy, ?_⟩
      simpa [bcFold] using hz
  | succ k ih =>
      intro hk hz
      obtain ⟨hV, hC, hZ⟩ := ih (by omega) hz
      have hjd : k + un < nc := by omega
      have htop : memGetDyn (bcFold up vp un nc k acc) (k + un) = 0 :=
        hZ (k + un) (by omega) (by omega)
      obtain ⟨hrowV, hrowC⟩ := bcRow_val up vp un nc k
        (bcFold up vp un nc k acc) hnc hjd hC htop
      have hvsucc : bignumVal (cells vp (k + 1))
          = bignumVal (cells vp k) + (memGetDyn vp k).toNat * (2 ^ 64) ^ k := by
        rw [cells_succ, bignumVal_snoc, cells_length]
      refine ⟨?_, ?_, ?_⟩
      · rw [bcFold_succ, hrowV, hV, hvsucc]
        ring
      · rw [bcFold_succ]; exact hrowC
      · intro i hi hin
        rw [bcFold_succ, bcRow_frame_gt up vp un nc k _ i hnc hin (by omega)]
        exact hZ i (by omega) hin

/-- **The `mpn_mul_basecase` contract.** Starting from an all-zero accumulator,
    the schoolbook fold leaves the product `up[0..un) · vp[0..vn)` in cells
    `0, …, un+vn-1`. -/
theorem bcFold_val_zero {NR NU NV : Nat} (up : Fin NU → BitVec 64)
    (vp : Fin NV → BitVec 64) (un vn : Nat) (acc : Fin NR → BitVec 64)
    (hnc : un + vn < NR) (hz : ∀ i, i < NR → memGetDyn acc i = 0) :
    bignumVal (cells (bcFold up vp un (un + vn) vn acc) (un + vn))
      = bignumVal (cells up un) * bignumVal (cells vp vn) := by
  obtain ⟨hV, _, _⟩ := bcFold_val up vp un (un + vn) acc hnc
    (hz _ hnc) vn (by omega) (fun i _ hin => hz i (by omega))
  rw [hV, bignumVal_cells_zero acc (un + vn) (fun i hi => hz i (by omega))]
  simp

/-- **The `mpn_sqr_basecase` contract.** The squaring specialisation is the same
    fold at `vp := up`, `vn := un`. -/
theorem bcFold_val_sqr {NR NU : Nat} (up : Fin NU → BitVec 64) (un : Nat)
    (acc : Fin NR → BitVec 64) (hnc : un + un < NR)
    (hz : ∀ i, i < NR → memGetDyn acc i = 0) :
    bignumVal (cells (bcFold up up un (un + un) un acc) (un + un))
      = bignumVal (cells up un) * bignumVal (cells up un) :=
  bcFold_val_zero up up un un acc hnc hz

/-! ## 4. The loop bodies as covered `LowCT`

The inner body runs over the catCryptDialect context
`Gbody = [rp : .memref NR, t : .sword 64, jd : .sword 64, up : .memref NU,
          vp : .memref NV, un : .sword 64, vn : .sword 64]` — the accumulator
array, the inner loop index, the outer loop index, then the four invariants. All
arithmetic is in the `srcClean` `SExpr` fragment (`SMul`, `SMulHiU`, `SAdd`,
`SSub`, `SAnd`, `SXor`, `SShr`), so `translateDialectControl` covers it. -/

/-- Limb count of the multiplicand array in the denotation model. -/
abbrev NU : Nat := 8

/-- Limb count of the multiplier array in the denotation model. -/
abbrev NV : Nat := 8

/-- Word count of the output array: `NU + NV` product words plus the scratch
    carry cell. -/
abbrev NR : Nat := NU + NV + 1

/-- The output-array slot `rp`, the loop accumulator. -/
def rpLoc : Located := ⟨"rp", .TBytes (8 * NR)⟩

/-- The multiplicand-array slot `up`, a loop invariant. -/
def upLoc : Located := ⟨"up", .TBytes (8 * NU)⟩

/-- The multiplier-array slot `vp`, a loop invariant. -/
def vpLoc : Located := ⟨"vp", .TBytes (8 * NV)⟩

/-- The inner trip count of every row: `un + 1` — the `un` addmul trips plus the
    flush trip. Recomputed from the loop-invariant `un` each outer pass. -/
def cntBodyLowCT : LowCT :=
  .RScalarSetExpr "cnt" (.SAdd (sv "un") (.SLit 1))

/-- One `mpn_addmul_1` position at the runtime indices `(jd, t)`: build the
    flush-trip mask from `bSltu t un`, read the masked multiplicand limb and the
    row scalar `vp[jd]`, form the widening product, add the running carry from
    the scratch cell `rp[un+vn]` and the destination word `rp[jd+t]`,
    synthesise both carry-out bits branch-free, then store the low word to
    `rp[jd+t]` and the new carry to the scratch cell. -/
def rowBodyLowCT : LowCT := seqAll (
  ltuCmds "kb" (sv "t") (sv "un")
  ++ [ .RScalarSetExpr "msk" (.SSub (.SLit 0) (sv "kb"))
     , .RScalarSetExpr "tm" (.SAnd (sv "t") (sv "msk"))
     , .RArrLoad ⟨"a0", .TU64⟩ upLoc "tm"
     , .RScalarSetExpr "a" (.SAnd (sv "a0") (sv "msk"))
     , .RArrLoad ⟨"vv", .TU64⟩ vpLoc "jd"
     , .RScalarSetExpr "lo" (.SMul (sv "a") (sv "vv"))
     , .RScalarSetExpr "hi" (.SMulHiU (sv "a") (sv "vv"))
     , .RScalarSetExpr "nc" (.SAdd (sv "un") (sv "vn"))
     , .RArrLoad ⟨"cy", .TU64⟩ rpLoc "nc"
     , .RScalarSetExpr "s1" (.SAdd (sv "lo") (sv "cy")) ]
  ++ ltuCmds "k1" (sv "s1") (sv "lo")
  ++ [ .RScalarSetExpr "pi" (.SAdd (sv "jd") (sv "t"))
     , .RArrLoad ⟨"rr", .TU64⟩ rpLoc "pi"
     , .RScalarSetExpr "s2" (.SAdd (sv "s1") (sv "rr")) ]
  ++ ltuCmds "k2" (sv "s2") (sv "s1")
  ++ [ .RScalarSetExpr "hc" (.SAdd (.SAdd (sv "hi") (sv "k1")) (sv "k2"))
     , .RArrStore rpLoc "pi" ⟨"s2", .TU64⟩
     , .RArrStore rpLoc "nc" ⟨"hc", .TU64⟩ ])

/-- The loop invariants: the two input arrays and the two runtime limb counts. -/
def Ginv : Ctx := [.memref NU, .memref NV, .sword 64, .sword 64]

/-- The inner-body context: accumulator, inner index, outer index, invariants. -/
def Gbody : Ctx := .memref NR :: .sword 64 :: .sword 64 :: Ginv

/-- The inner-count-body context: outer index, invariants. -/
def Gcount : Ctx := .sword 64 :: Ginv

/-- The inner-body `VarMap`: `vn` bound deepest, then `un`, `vp`, `up`, `jd`,
    `t`, and `rp` at `.here`. -/
def vmBody : VarMap Gbody :=
  ((((((VarMap.empty.bind (t := .sword 64) "vn").bind
      (t := .sword 64) "un").bind
      (t := .memref NV) "vp").bind
      (t := .memref NU) "up").bind
      (t := .sword 64) "jd").bind
      (t := .sword 64) "t").bind (t := .memref NR) "rp"

/-- The inner-count-body `VarMap`. -/
def vmCount : VarMap Gcount :=
  ((((VarMap.empty.bind (t := .sword 64) "vn").bind
      (t := .sword 64) "un").bind
      (t := .memref NV) "vp").bind
      (t := .memref NU) "up").bind (t := .sword 64) "jd"

/-! ## 5. The nested runtime-trip loop program

Outer argument context `[vn, un, vp, up, rp]` (newest first), routing
`rp → RDI`, `up → RSI`, `vp → RDX`, `un → RCX`, `vn → R8`. -/

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The output-array jasmin type. -/
abbrev AR : JasminTy := .stackArr 64 NR

/-- The multiplicand-array jasmin type. -/
abbrev AU : JasminTy := .stackArr 64 NU

/-- The multiplier-array jasmin type. -/
abbrev AV : JasminTy := .stackArr 64 NV

/-- The kernel's outer argument context, newest first. -/
abbrev Gouter : Ctxt jasminDialect := [r64, r64, AV, AU, AR]

/-- The runtime outer trip count `vn` (R8). -/
def bcOuterCount : Ctxt.Var Gouter r64 := .here

/-- The accumulator seed: the output array `rp` (RDI). -/
def bcInit : Ctxt.Var Gouter AR := .there (.there (.there (.there .here)))

/-- The loop invariants: `up` (RSI), `vp` (RDX), `un` (RCX) and `vn` (R8). -/
def bcInvs : HVector (fun ty => Ctxt.Var Gouter ty) [AU, AV, r64, r64] :=
  .cons (.there (.there (.there .here)))
    (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil)))

/-- The front-compiled nested runtime-trip `mpn_mul_basecase`: one inner body
    copy behind two `jne` back-edges, the outer trip counter seeded from the
    runtime `vn` register, the inner trip recomputed as `un + 1` each outer
    pass, the output array threaded as the loop accumulator and `up`/`vp`/`un`/
    `vn` as loop invariants. `none` if either front declines. -/
def bcProgOpt : Option (ComL Gouter AR) :=
  Dialects.FrontRoutePlan.compileNested (Γouter := Gouter) (accCTy := .memref NR)
    (invCTys := Ginv) .plain
    vmCount "cnt" cntBodyLowCT
    vmBody "rp" rowBodyLowCT
    bcOuterCount bcInit bcInvs

-- The front accepts both bodies and wraps them in a `ComL.forLoopNRtNested`.
#guard bcProgOpt.isSome

-- The spine is the nested runtime-loop node, not an unrolled inner sweep.
#guard (bcProgOpt.map (fun c => match c with
  | .forLoopNRtNested _ _ _ _ _ _ => true
  | _ => false)) = some true

/-- **The emitted nest's denotation is the `JLoopBodyN.nestedDenote` double fold
    of the front bodies.** Whenever the front compiles `cntBodyLowCT` to
    `innerCount` and `rowBodyLowCT` to `innerUpdate`, the program's denotation at
    any valuation is the outer fold over `vn` rows of the inner fold over the
    recomputed trip count, seeded by the `rp` argument and threading the
    invariants. The instance of `rolledForLoopNRtNested_denote` at this
    kernel. -/
theorem bcProg_denote
    {innerCount : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.sword 64 :: Ginv))
      (CryptoToJasminCom.mapTy (CryptoTy.sword 64))}
    {innerUpdate : Com jasminDialect
      (CryptoToJasminCom.mapCtx
        (CryptoTy.memref NR :: .sword 64 :: .sword 64 :: Ginv))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NR))}
    (hcnt : Dialects.TranslateDialectRolledLoop.frontLoopBodyJ
      (accCTy := .sword 64) (Γbody := .sword 64 :: Ginv)
      vmCount "cnt" cntBodyLowCT = some innerCount)
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJ
      (accCTy := .memref NR)
      (Γbody := CryptoTy.memref NR :: .sword 64 :: .sword 64 :: Ginv)
      vmBody "rp" rowBodyLowCT = some innerUpdate)
    (V : Ctxt.Valuation Gouter) :
    bcProgOpt.map (fun c => ComL.denote c V)
      = some (JLoopBodyN.nestedDenote innerCount innerUpdate
          (bcOuterCount.lookup V).toNat (Expr.lookupArgs bcInvs V)
          (bcInit.lookup V)) :=
  rolledForLoopNRtNested_denote vmCount "cnt" cntBodyLowCT vmBody "rp" rowBodyLowCT
    bcOuterCount bcInit bcInvs hcnt hupd V

/-! ## 6. The owned `Lprog` and the rendered `.s` -/

/-- The rolled, owned-RA 5-argument-ABI `Lprog` for the runtime-trip
    `mpn_mul_basecase` under the C symbol `fname`
    (`RDI = rp`, `RSI = up`, `RDX = vp`, `RCX = un`, `R8 = vn`).

    The `MULXHI` high-word binding the front emits for `SMulHiU` is coalesced
    with its paired low `MUL` into the printer's two-output `mulx` by
    `FheMontMulEmit.fuseMulHiLprog` in its `saveRdx` looped-body mode: the
    kernel's multiply sits inside two back-edges, so `%rdx` is saved and
    restored around the pinned multiplicand. -/
def bcRtLprogOpt (fname : String) : Option Lprog :=
  bcProgOpt.map (fun c =>
    FheMontMulEmit.fuseMulHiLprog
      (ComL.toLprogPhysAbi c fname (argName 0) [argName 1, argName 2]
        (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX", "R8"]
        [64, 64, 64, 64, 64])
      (saveRdx := true))

/-- The owned AT&T `.s` text for the runtime-trip `mpn_mul_basecase`. -/
def bcRtAsmOpt (fname : String) : Option String :=
  (bcRtLprogOpt fname).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

/-- The 5-argument-ABI physical body of the front-compiled nested loop. -/
def bcRtPhysBodyOpt : Option Lcmd :=
  bcProgOpt.map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1, argName 2]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX", "R8"]
      [64, 64, 64, 64, 64]).lfd_body)

-- The physical body carries two bottom-test back-edges: the outer row loop and
-- the inner limb loop, so the emit is a nest and not an unrolled chain.
#guard (bcRtPhysBodyOpt.map (fun body =>
  (body.filter (fun i => match i.li_i with
    | .Lcond (.reg "NZ") _ => true | _ => false)).length)) = some 2

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would
-- re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 7. Emit driver

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency.

`mpn_sqr_basecase` is this kernel at `vp := up`, `vn := un` — the specialisation
`bcFold_val_sqr` states — so one file is written and the squaring caller passes
the same pointer twice. -/

/-- Write the owned-backend `.s` for the nested runtime-trip `mpn_mul_basecase`
    into the `bench/mpn_mulbase_front_compare/gen_com` harness directory. -/
def emitMain : IO Unit := do
  let dir := "bench/mpn_mulbase_front_compare/gen_com"
  IO.FS.createDirAll dir
  match bcRtAsmOpt "mpn_mul_basecase_rt" with
  | some s =>
      IO.FS.writeFile (dir ++ "/mpn_mul_basecase_rt_owned.s") s
      IO.println "WROTE bench/mpn_mulbase_front_compare/gen_com/mpn_mul_basecase_rt_owned.s"
  | none => throw (IO.userError "the nested runtime-loop front declined mpn_mul_basecase")

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
