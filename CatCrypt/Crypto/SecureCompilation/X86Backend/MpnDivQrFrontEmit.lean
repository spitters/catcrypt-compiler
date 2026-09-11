/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan

/-!
# `mpn_div_qr` (Knuth Algorithm D) as a front-generated nested runtime-trip loop

`mpn_div_qr_preinv(wp, vp, qn, vn, dinv)` divides the `qn + vn - 1`-limb
dividend held in the window cells `wp[0 .. qn+vn-1]` by the `vn`-limb divisor
`vp[0 .. vn)`, leaving the `qn` quotient limbs in `wp[qn+vn .. 2qn+vn)` and
the `vn` remainder limbs in `wp[0 .. vn)`. This is the general multi-limb
division of GMP's `mpn_tdiv_qr` (Knuth TAOCP Vol. 2 §4.3.1, Algorithm D),
sourced through the verified nested runtime-loop front: the per-trip body is
covered `LowCT`, and the rolled-loop dispatcher's nested route
(`Dialects.FrontRoutePlan.compileNested` at the `plain` body front)
front-compiles it together with an inner-trip-count body and wraps them in a
`ComL.forLoopNRtNested`.

```
  kdBodyLowCT (RArrLoad wp/vp at runtime indices, preinvStep q̂ estimate,
               submul/add-back word steps, mask-selected RArrStore targets)
    --(compileNested .plain)----> ComL.forLoopNRtNested
    --(ComL.toLprogPhysAbi / renderLprogAtt)-----------> AT&T .s
```

## The phase-merged inner loop

Algorithm D's per-digit work is a scalar q̂ estimate followed by two dependent
inner sweeps (multiply-subtract, then a conditional add-back). The nested
runtime-loop front carries ONE inner body per outer trip, so the digit is
expressed as a single phase-merged inner loop of `2·vn + 3` trips selected by
branch-free masks on the inner trip index `t`:

* trip `t = 0` — the q̂ phase: the Möller–Granlund reciprocal step
  (`preinvStep`) divides the window's top two limbs by the top divisor limb,
  the `u₂ = v₁` special case selects `q̂ = 2^64 - 1` with `r̂ = u₁ + v₁`
  (its 65th bit tracked separately), and two branch-free Knuth-D3 refinement
  rounds test `q̂·v₂ > r̂·2^64 + u₀` and correct down. The refined q̂ is
  stored to a scratch cell; the borrow and carry cells are zeroed.
* trips `1 ≤ t ≤ vn+1` — the submul phase: limb `i = t - 1` of
  `window − q̂·divisor`, the divisor limb read masked to `0` at the top trip
  `i = vn`, the running borrow riding in a scratch cell.
* trips `vn+2 ≤ t ≤ 2vn+2` — the add-back phase: limb `i = t - vn - 2` of
  `window + (borrow ≠ 0 ? divisor : 0)`, the running carry riding in a
  scratch cell, and the digit `q̂ − (borrow ≠ 0)` written to the quotient
  cell.

Every phase's values are computed every trip; mask-selected store indices
route the inactive phases' writes to dummy scratch cells. An outer body of
the shape "scalar prologue, then two sibling inner loops" would emit
Algorithm D at its native shape; no rolled route covers that combination (the
nested route's outer pass is exactly one inner node — see
`FrontRoutePlan.RouteGap`), so the phase-merged body is how the covered
fragment expresses the digit today, at a `(2vn+3)/(2vn)`-trip and
full-body-per-trip runtime cost over the native shape.

## The accumulator layout

`JLoopBodyN` carries ONE accumulator, so the window, the quotient and the
scratch state share the array `wp`, at runtime-computed offsets (no
compile-time size leaks into the ABI):

```
  wp[0 .. qn+vn-1]              window (dividend, becomes the remainder)
  wp[qn+vn .. 2qn+vn)           quotient limbs (digit j at wp[qn+vn+j])
  wp[2qn+vn]                    q̂ scratch
  wp[2qn+vn+1]                  submul borrow scratch
  wp[2qn+vn+2]                  add-back carry scratch
  wp[2qn+vn+3], wp[2qn+vn+4]    dummy store targets for masked-off phases
```

`wp` therefore holds `2qn + vn + 5` words. The outer loop counts `jd` up
from `0`; the digit base is `j = qn - 1 - jd`, descending as Algorithm D
requires.

## ABI

```c
extern uint64_t *mpn_div_qr_preinv(uint64_t *wp, const uint64_t *vp,
                                   uint64_t qn, uint64_t vn, uint64_t dinv);
```

`wp` (RDI), `vp` (RSI), `qn` (RDX), `vn` (RCX), `dinv` (R8). Preconditions
(the caller normalises, exactly as for `mpn_divrem_1_preinv`): `vn ≥ 2`,
`qn ≥ 1`, the divisor's top limb has bit 63 set, `dinv` is its
Möller–Granlund reciprocal (`preinvOf`), and the window value is below
`divisor · 2^(64·qn)` (the appended top window cell after the normalising
shift guarantees this). The normalising shift itself is
`mpn_lshift`/`mpn_rshift` (`MpnShiftFrontEmit`) plus one `clz`, composed by
the C caller; the covered `SExpr` fragment has no leading-zero-count
operator, so normalisation stays a caller obligation rather than being
hand-authored around the front.

## Main results

* `natLimbs` / `bignumVal_natLimbs`: the little-endian limb decomposition of
  a `Nat` and its recombination.
* `setSeg` and its read lemmas: writing a limb list into a memref segment.
* `kdDigitStep` / `kdFold`: the exact per-digit division step on the memref
  carrier — window `W` becomes `W % D` and the digit `W / D` lands in the
  quotient cell — and its fold over the descending digit index.
* `kdFold_val`: the Algorithm D loop invariant — after `k` digits the
  remaining window `R` satisfies `Q · D · 2^(64(qn-k)) + R = N₀` and
  `R < D · 2^(64(qn-k))`.
* `kdFold_div_qr`: the Euclidean division contract at `k = qn` —
  `quotient · divisor + remainder = dividend` and `remainder < divisor`, at
  `bignumVal` recombination.
* `kdTripStep` / `kdInner`: the word function the emitted body computes,
  transcribed op for op from `kdBodyLowCT`.
* `KdDigitAgrees`: the `Prop` identifying one digit's trip fold with
  `kdDigitStep` on the observable region, under the normalisation
  preconditions. Stated, not discharged, here; its proof composes Knuth
  Theorem B (`Mpn.QhatBound`) with the limb-level digit correctness
  (`Mpn.DivRemKnuth.submulAddBackDigit_spec`).
* `kdProgOpt` / `kdProg_denote`: the front-compiled nested runtime-trip
  program and its denotation as the `JLoopBodyN.nestedDenote` double fold.
* `kdLprogOpt` / `kdAsmOpt`: the owned `Lprog` and the rendered AT&T `.s`,
  with the front-acceptance, loop-spine, back-edge and render gates enforced
  by `emitMain` (which throws, failing elaboration, when any gate fails).

## Scope

`kdFold_val` and `kdFold_div_qr` hold for every `NW` / `NV` and every
runtime `qn` / `vn` / `qbase`; the concrete front-compiled instance below
fixes only the memref widths of the denotation model, and the rendered SIB
accesses are byte-offset and so size-agnostic.

`kdFold_val` is a statement about the arithmetic model `kdDigitStep`, the
exact Euclidean digit. `kdTripStep` is the word function the emitted body
computes. `KdDigitAgrees` is the `Prop` recording their identification under
the normalisation preconditions; it is stated, not discharged, here — the
same seam `MpnDivRem1FrontEmit.PreinvStepAgrees` leaves open for the
single-limb kernel. Whole-division value checks against reference vectors
belong in the external bench harness
(`bench/mpn_divqr_front_compare`); a `kdTripStep` fold deeper than a few
trips must not be evaluated by `#eval` or `#guard` in Lean — the evaluator
re-forces the memref closure chain without sharing and the check stalls the
build.

`kdProg_denote` carries the two front-compilation hypotheses and concludes
at `JLoopBodyN.nestedDenote` of the front bodies. Identifying that
denotation with `kdTripStep` — so that `kdFold_val` reads as a statement
about the emitted kernel — is the separate source-preservation step
(`translateDialectControl_denote_ctl` composed with
`cryptoDialectToJasminCom`), not established here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivQrFrontEmit

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
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal bignumVal_lt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (cells cells_length memGetDyn_memSetDyn_ne memGetDyn_memSetDyn_self
   seqAll ltuCmds sv notE ones)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
  (segCells segCells_cons preinvStep preinvOf)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-! ## 1. Limb decomposition and segment writes -/

/-- The first `k` little-endian base-`2^64` limbs of a `Nat`. -/
def natLimbs : Nat → Nat → List (BitVec 64)
  | _, 0 => []
  | r, k + 1 => BitVec.ofNat 64 r :: natLimbs (r / 2 ^ 64) k

/-- `natLimbs r k` has length `k`. -/
theorem natLimbs_length (r k : Nat) : (natLimbs r k).length = k := by
  induction k generalizing r with
  | zero => rfl
  | succ m ih => simp [natLimbs, ih]

/-- The limbs of a `Nat` below `2^(64k)` recombine to it. -/
theorem bignumVal_natLimbs (r k : Nat) (h : r < (2 ^ 64) ^ k) :
    bignumVal (natLimbs r k) = r := by
  induction k generalizing r with
  | zero => simp only [pow_zero, Nat.lt_one_iff] at h; simp [natLimbs, bignumVal, h]
  | succ m ih =>
      have hdiv : r / 2 ^ 64 < (2 ^ 64) ^ m := by
        refine Nat.div_lt_of_lt_mul ?_
        rw [pow_succ] at h
        omega
      simp only [natLimbs, bignumVal, BitVec.toNat_ofNat, ih (r / 2 ^ 64) hdiv]
      exact Nat.mod_add_div r (2 ^ 64)

/-- A prefix of a limb decomposition is the shorter decomposition. -/
theorem natLimbs_take (r k m : Nat) (h : m ≤ k) :
    (natLimbs r k).take m = natLimbs r m := by
  induction m generalizing r k with
  | zero => rfl
  | succ i ih =>
      cases k with
      | zero => omega
      | succ n =>
          simp only [natLimbs, List.take_succ_cons]
          rw [ih (r / 2 ^ 64) n (by omega)]

/-- Write a limb list into consecutive memref cells starting at `lo`. -/
def setSeg {N : Nat} : (Fin N → BitVec 64) → Nat → List (BitVec 64) →
    Fin N → BitVec 64
  | acc, _, [] => acc
  | acc, lo, v :: vs => setSeg (memSetDyn acc lo v) (lo + 1) vs

/-- Cells below the written segment are unchanged. -/
theorem setSeg_get_lt {N : Nat} (acc : Fin N → BitVec 64) (lo : Nat)
    (vs : List (BitVec 64)) (i : Nat) (hi : i < lo) (hb : lo + vs.length ≤ N) :
    memGetDyn (setSeg acc lo vs) i = memGetDyn acc i := by
  induction vs generalizing acc lo with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.length_cons] at hb
      rw [setSeg, ih _ (lo + 1) (by omega) (by omega),
        memGetDyn_memSetDyn_ne _ lo i _ (by omega) (by omega) (by omega)]

/-- Cells at or above the written segment's end are unchanged. -/
theorem setSeg_get_ge {N : Nat} (acc : Fin N → BitVec 64) (lo : Nat)
    (vs : List (BitVec 64)) (i : Nat) (hi : lo + vs.length ≤ i) (hiN : i < N) :
    memGetDyn (setSeg acc lo vs) i = memGetDyn acc i := by
  induction vs generalizing acc lo with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.length_cons] at hi
      rw [setSeg, ih _ (lo + 1) (by omega),
        memGetDyn_memSetDyn_ne _ lo i _ (by omega) hiN (by omega)]

/-- Reading a prefix of a written segment returns the written limbs. -/
theorem segCells_setSeg {N : Nat} (acc : Fin N → BitVec 64) (lo : Nat)
    (vs : List (BitVec 64)) (k : Nat) (hk : k ≤ vs.length)
    (hb : lo + vs.length ≤ N) :
    segCells (setSeg acc lo vs) lo k = vs.take k := by
  induction k generalizing acc lo vs with
  | zero => simp [segCells]
  | succ m ih =>
      cases vs with
      | nil => simp at hk
      | cons v vs =>
          simp only [List.length_cons] at hk hb
          rw [segCells_cons, setSeg, List.take_succ_cons]
          congr 1
          · rw [setSeg_get_lt _ (lo + 1) vs lo (by omega) (by omega),
              memGetDyn_memSetDyn_self _ lo v (by omega)]
          · exact ih _ (lo + 1) vs (by omega) (by omega)

/-- A write at an index at or above a segment's end is invisible to it. -/
theorem segCells_setDyn_of_ge {N : Nat} (arr : Fin N → BitVec 64)
    (lo k idx : Nat) (w : BitVec 64) (hge : lo + k ≤ idx) (hidx : idx < N) :
    segCells (memSetDyn arr idx w) lo k = segCells arr lo k := by
  simp only [segCells, List.map_inj_left, List.mem_range]
  intro i hi
  exact memGetDyn_memSetDyn_ne _ idx (lo + i) _ hidx (by omega) (by omega)

/-- A memref prefix of a sum length splits as prefix plus segment. -/
theorem cells_add {N : Nat} (arr : Fin N → BitVec 64) (a b : Nat) :
    cells arr (a + b) = cells arr a ++ segCells arr a b := by
  unfold cells segCells
  rw [List.range_add, List.map_append, List.map_map]
  rfl

/-- `bignumVal` of an append weights the suffix by the prefix length. -/
theorem bignumVal_append (xs ys : List (BitVec 64)) :
    bignumVal (xs ++ ys) = bignumVal xs + (2 ^ 64) ^ xs.length * bignumVal ys := by
  induction xs with
  | nil => simp [bignumVal]
  | cons x xs ih =>
      simp only [List.cons_append, bignumVal, ih, List.length_cons, pow_succ]
      ring

/-! ## 2. The exact quotient-digit step and the Algorithm D fold

The emitted nest carries the whole work array as its accumulator; one outer
trip processes one quotient digit. `kdDigitStep` is the digit's exact
arithmetic effect on the array and `kdFold` folds it over the descending
digit index, the `(List.range qn).foldl` shape `JLoopBodyN.nestedDenote`'s
outer fold takes. -/

/-- One exact quotient digit at window base `j`: the `vn + 1`-cell window
    value `W` is divided by the divisor value `D`; the window cells become
    the limbs of `W % D` (top limb `0`) and the digit `W / D` is written to
    the quotient cell `qbase + j`. -/
def kdDigitStep {NW NV : Nat} (vp : Fin NV → BitVec 64) (vn qbase : Nat)
    (acc : Fin NW → BitVec 64) (j : Nat) : Fin NW → BitVec 64 :=
  let D := bignumVal (cells vp vn)
  let W := bignumVal (segCells acc j (vn + 1))
  memSetDyn (setSeg acc j (natLimbs (W % D) (vn + 1)))
    (qbase + j) (BitVec.ofNat 64 (W / D))

/-- The Algorithm D fold: `k` exact digit steps at the descending bases
    `qn - 1, qn - 2, …, qn - k`. -/
def kdFold {NW NV : Nat} (vp : Fin NV → BitVec 64) (vn qbase qn : Nat)
    (k : Nat) (acc : Fin NW → BitVec 64) : Fin NW → BitVec 64 :=
  (List.range k).foldl (fun a s => kdDigitStep vp vn qbase a (qn - 1 - s)) acc

/-- The fold peels its last digit. -/
theorem kdFold_succ {NW NV : Nat} (vp : Fin NV → BitVec 64) (vn qbase qn k : Nat)
    (acc : Fin NW → BitVec 64) :
    kdFold vp vn qbase qn (k + 1) acc
      = kdDigitStep vp vn qbase (kdFold vp vn qbase qn k acc) (qn - 1 - k) := by
  simp [kdFold, List.range_succ]

/-- **The Algorithm D loop invariant.** After `k` digits the quotient cells
    `qbase + qn - k, …, qbase + qn - 1` hold the top `k` quotient digits, the
    remaining window `R` is below `D · 2^(64(qn-k))`, and
    `Q · D · 2^(64(qn-k)) + R` recombines to the original window value. -/
theorem kdFold_val {NW NV : Nat} (vp : Fin NV → BitVec 64) (vn qbase qn : Nat)
    (acc : Fin NW → BitVec 64)
    (hqb : qn + vn ≤ qbase) (hNW : qbase + qn ≤ NW)
    (hD : 0 < bignumVal (cells vp vn))
    (hR0 : bignumVal (cells acc (qn + vn))
             < bignumVal (cells vp vn) * (2 ^ 64) ^ qn) :
    ∀ k : Nat, k ≤ qn →
      bignumVal (cells (kdFold vp vn qbase qn k acc) (qn + vn - k))
          < bignumVal (cells vp vn) * (2 ^ 64) ^ (qn - k)
        ∧ bignumVal (segCells (kdFold vp vn qbase qn k acc) (qbase + (qn - k)) k)
              * (bignumVal (cells vp vn) * (2 ^ 64) ^ (qn - k))
            + bignumVal (cells (kdFold vp vn qbase qn k acc) (qn + vn - k))
          = bignumVal (cells acc (qn + vn)) := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨by simpa [kdFold] using hR0, ?_⟩
      simp [kdFold, segCells, bignumVal]
  | succ k ih =>
      intro hk1
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      set D := bignumVal (cells vp vn) with hDdef
      set F := kdFold vp vn qbase qn k acc with hFdef
      set j := qn - 1 - k with hjdef
      have hj : qn - k = j + 1 := by omega
      set W := bignumVal (segCells F j (vn + 1)) with hWdef
      have hlen_idx : qn + vn - k = j + (vn + 1) := by omega
      have hsplitk : bignumVal (cells F (qn + vn - k))
          = bignumVal (cells F j) + (2 ^ 64) ^ j * W := by
        rw [hlen_idx, cells_add, bignumVal_append, cells_length]
      set L := bignumVal (cells F j) with hLdef
      have hL : L < (2 ^ 64) ^ j := by
        have h := bignumVal_lt (cells F j)
        rwa [cells_length] at h
      have hpow : (2 ^ 64 : Nat) ^ (qn - k) = (2 ^ 64) ^ j * 2 ^ 64 := by
        rw [hj, pow_succ]
      have hWlt : W < D * 2 ^ 64 := by
        rcases Nat.lt_or_ge W (D * 2 ^ 64) with h | hcon
        · exact h
        · exfalso
          have hmul : (2 ^ 64 : Nat) ^ j * (D * 2 ^ 64) ≤ (2 ^ 64) ^ j * W :=
            Nat.mul_le_mul_left _ hcon
          have hRk := ih1
          rw [hsplitk, hpow] at hRk
          nlinarith [hmul, hRk, Nat.zero_le L]
      have hq_lt : W / D < 2 ^ 64 := Nat.div_lt_of_lt_mul hWlt
      have hr_lt : W % D < D := Nat.mod_lt _ hD
      have hDvn : D < (2 ^ 64) ^ vn := by
        have h := bignumVal_lt (cells vp vn)
        rwa [cells_length] at h
      have hr_vn : W % D < (2 ^ 64) ^ vn := lt_trans hr_lt hDvn
      have hqcell : qbase + j < NW := by omega
      set RL := natLimbs (W % D) (vn + 1) with hRLdef
      have hRLlen : RL.length = vn + 1 := natLimbs_length _ _
      set qbv := BitVec.ofNat 64 (W / D) with hqbvdef
      set F' := memSetDyn (setSeg F j RL) (qbase + j) qbv with hF'def
      have hstep : kdFold vp vn qbase qn (k + 1) acc = F' := by
        rw [kdFold_succ]
        rfl
      have hlow : cells F' j = cells F j := by
        simp only [hF'def, cells, List.map_inj_left, List.mem_range]
        intro i hi
        rw [memGetDyn_memSetDyn_ne _ (qbase + j) i qbv hqcell (by omega) (by omega),
          setSeg_get_lt F j RL i hi (by rw [hRLlen]; omega)]
      have hwin : segCells F' j vn = natLimbs (W % D) vn := by
        rw [hF'def, segCells_setDyn_of_ge _ j vn (qbase + j) qbv (by omega) hqcell,
          segCells_setSeg F j RL vn (by rw [hRLlen]; omega) (by rw [hRLlen]; omega),
          hRLdef, natLimbs_take _ _ _ (by omega)]
      have hRk1 : bignumVal (cells F' (j + vn)) = L + (2 ^ 64) ^ j * (W % D) := by
        rw [cells_add, bignumVal_append, cells_length, hlow, hwin,
          bignumVal_natLimbs _ _ hr_vn]
      have hqold : segCells F' (qbase + j + 1) k = segCells F (qbase + j + 1) k := by
        simp only [hF'def, segCells, List.map_inj_left, List.mem_range]
        intro i hi
        rw [memGetDyn_memSetDyn_ne _ (qbase + j) (qbase + j + 1 + i) qbv hqcell
            (by omega) (by omega),
          setSeg_get_ge F j RL _ (by rw [hRLlen]; omega) (by omega)]
      have hqnew : memGetDyn F' (qbase + j) = qbv :=
        memGetDyn_memSetDyn_self _ _ _ hqcell
      set Qk := bignumVal (segCells F (qbase + j + 1) k) with hQkdef
      have hQ1 : bignumVal (segCells F' (qbase + j) (k + 1)) = W / D + 2 ^ 64 * Qk := by
        rw [segCells_cons, hqnew]
        simp only [bignumVal, hqold, hqbvdef, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hq_lt]
        rfl
      have hidx1 : qn - (k + 1) = j := by omega
      have hidx2 : qn + vn - (k + 1) = j + vn := by omega
      have hqk : qbase + (qn - k) = qbase + j + 1 := by omega
      have hih2 : Qk * (D * ((2 ^ 64) ^ j * 2 ^ 64)) + (L + (2 ^ 64) ^ j * W)
          = bignumVal (cells acc (qn + vn)) := by
        have h := ih2
        rw [hqk, hpow, hsplitk] at h
        exact h
      rw [hstep]
      refine ⟨?_, ?_⟩
      · rw [hidx2, hidx1, hRk1]
        calc L + (2 ^ 64) ^ j * (W % D)
            < (2 ^ 64) ^ j + (2 ^ 64) ^ j * (W % D) := by omega
          _ = (2 ^ 64) ^ j * (W % D + 1) := by ring
          _ ≤ (2 ^ 64) ^ j * D := Nat.mul_le_mul_left _ (by omega)
          _ = D * (2 ^ 64) ^ j := Nat.mul_comm _ _
      · rw [hidx2, hidx1, hRk1, hQ1]
        have hdm : D * (W / D) + W % D = W := Nat.div_add_mod W D
        calc (W / D + 2 ^ 64 * Qk) * (D * (2 ^ 64) ^ j)
              + (L + (2 ^ 64) ^ j * (W % D))
            = Qk * (D * ((2 ^ 64) ^ j * 2 ^ 64))
              + (L + (2 ^ 64) ^ j * (D * (W / D) + W % D)) := by ring
          _ = Qk * (D * ((2 ^ 64) ^ j * 2 ^ 64)) + (L + (2 ^ 64) ^ j * W) := by
              rw [hdm]
          _ = bignumVal (cells acc (qn + vn)) := hih2

/-- **The Euclidean division contract.** After all `qn` digits the quotient
    cells and the remaining `vn`-cell window recombine to
    `quotient · divisor + remainder = dividend` with `remainder < divisor`. -/
theorem kdFold_div_qr {NW NV : Nat} (vp : Fin NV → BitVec 64) (vn qbase qn : Nat)
    (acc : Fin NW → BitVec 64)
    (hqb : qn + vn ≤ qbase) (hNW : qbase + qn ≤ NW)
    (hD : 0 < bignumVal (cells vp vn))
    (hR0 : bignumVal (cells acc (qn + vn))
             < bignumVal (cells vp vn) * (2 ^ 64) ^ qn) :
    bignumVal (segCells (kdFold vp vn qbase qn qn acc) qbase qn)
          * bignumVal (cells vp vn)
        + bignumVal (cells (kdFold vp vn qbase qn qn acc) vn)
      = bignumVal (cells acc (qn + vn))
    ∧ bignumVal (cells (kdFold vp vn qbase qn qn acc) vn)
        < bignumVal (cells vp vn) := by
  obtain ⟨h1, h2⟩ := kdFold_val vp vn qbase qn acc hqb hNW hD hR0 qn (Nat.le_refl _)
  simp only [Nat.sub_self, pow_zero, Nat.mul_one, Nat.add_zero] at h1 h2
  rw [show qn + vn - qn = vn from by omega] at h1 h2
  exact ⟨h2, h1⟩

/-! ## 3. The word function the emitted body computes

`kdTripStep` transcribes `kdBodyLowCT` op for op over the memref carrier;
`kdInner` is one digit's `2·vn + 3` trips. All scalar arithmetic is
`BitVec 64` (wrapping), matching the register semantics of the emitted body;
the clamped indices keep every load in bounds at the trips where a phase's
index expression underflows. -/

/-- Branch-free select: `b ^^^ ((a ^^^ b) &&& m)` is `a` under the all-ones
    mask and `b` under the zero mask. -/
def xselW (m a b : BitVec 64) : BitVec 64 := b ^^^ ((a ^^^ b) &&& m)

/-- One Knuth-D3 refinement round on `(q̂, r̂, r̂-carry)`: subtract
    `q̂·v₂` from the 128-bit `(r̂, u₀)` and decrement q̂ on borrow-out,
    adding `v₁` back into r̂ and folding its carry into the r̂-carry bit.
    Inert when the r̂-carry is already set. The round-2 instance's r̂ and
    carry outputs are dead. -/
def kdRefineRound (d1 d2 u0 : BitVec 64) (s : BitVec 64 × BitVec 64 × BitVec 64) :
    BitVec 64 × BitVec 64 × BitVec 64 :=
  let qhat := s.1
  let rhat := s.2.1
  let rc := s.2.2
  let lo := qhat * d2
  let b1 := bSltu u0 lo
  let tt := rhat - mulHiW qhat d2
  let b2 := bSltu rhat (mulHiW qhat d2)
  let b3 := bSltu tt b1
  let gt := b2 ^^^ b3
  let doit := gt &&& (rc ^^^ 1)
  let md := (0 : BitVec 64) - doit
  let qhat' := qhat - doit
  let rhat' := rhat + (d1 &&& md)
  let cc := (bSltu rhat' rhat) &&& doit
  (qhat', rhat', rc ^^^ cc)

/-- One inner trip of the phase-merged Algorithm D body, at outer trip `jdW`
    and inner trip `tW`: the q̂ phase (`t = 0`), the submul phase
    (`1 ≤ t ≤ vn+1`) and the add-back phase (`t ≥ vn+2`) are all computed;
    the mask-selected store indices route the inactive phases' writes to the
    dummy scratch cells. The op-for-op word transcription of
    `kdBodyLowCT`. -/
def kdTripStep {NW NV : Nat} (vp : Fin NV → BitVec 64)
    (vnW qnW dinv : BitVec 64) (acc : Fin NW → BitVec 64)
    (jdW tW : BitVec 64) : Fin NW → BitVec 64 :=
  let j := qnW - 1 - jdW
  let un1 := qnW + vnW
  let sq := un1 + qnW
  let sb := sq + 1
  let sc := sq + 2
  let du := sq + 3
  let du2 := sq + 4
  let pQ := bSltu tW 1
  let pSr := bSltu tW (vnW + 2)
  let pS := pSr &&& (pQ ^^^ 1)
  let pA := pSr ^^^ 1
  let mQ := (0 : BitVec 64) - pQ
  let mS := (0 : BitVec 64) - pS
  let mA := (0 : BitVec 64) - pA
  let jvn := j + vnW
  let u2 := memGetDyn acc jvn.toNat
  let u1 := memGetDyn acc (jvn - 1).toNat
  let u0 := memGetDyn acc (jvn - 2).toNat
  let d1 := memGetDyn vp (vnW - 1).toNat
  let d2 := memGetDyn vp (vnW - 2).toNat
  let pr := preinvStep dinv d1 u2 u1
  let pe := bSltu u2 d1
  let meq := (0 : BitVec 64) - (pe ^^^ 1)
  let rsp := u1 + d1
  let rc0 := (bSltu rsp u1) &&& (pe ^^^ 1)
  let qh0 := xselW meq (BitVec.allOnes 64) pr.1
  let rh0 := xselW meq rsp pr.2
  let s1r := kdRefineRound d1 d2 u0 (qh0, rh0, rc0)
  let s2r := kdRefineRound d1 d2 u0 s1r
  let qh2 := s2r.1
  let iS := tW - 1
  let mcs := (0 : BitVec 64) - bSltu iS (vnW + 1)
  let iScl := iS &&& mcs
  let mv := (0 : BitVec 64) - bSltu iS vnW
  let vi := (memGetDyn vp (iS &&& mv).toNat) &&& mv
  let qhS := memGetDyn acc sq.toNat
  let bin := memGetDyn acc sb.toNat
  let wix := j + iScl
  let wcell := memGetDyn acc wix.toNat
  let plo := qhS * vi
  let phi := mulHiW qhS vi
  let t1 := wcell - bin
  let b1s := bSltu wcell bin
  let t2 := t1 - plo
  let b2s := bSltu t1 plo
  let bout := phi + b1s + b2s
  let iA := tW - (vnW + 2)
  let mca := (0 : BitVec 64) - bSltu iA (vnW + 1)
  let iAcl := iA &&& mca
  let mva := (0 : BitVec 64) - bSltu iA vnW
  let va := (memGetDyn vp (iA &&& mva).toNat) &&& mva
  let bnz := bSltu 0 bin
  let mB := (0 : BitVec 64) - bnz
  let av := va &&& mB
  let cin := memGetDyn acc sc.toNat
  let aix := j + iAcl
  let acell := memGetDyn acc aix.toNat
  let sm1 := acell + av
  let c1a := bSltu sm1 acell
  let sm2 := sm1 + cin
  let c2a := bSltu sm2 sm1
  let cout := c1a + c2a
  let qv := qhS - bnz
  let qix := un1 + j
  let wSelIx := (du &&& mQ) ^^^ (wix &&& mS) ^^^ (aix &&& mA)
  let wSelV := (t2 &&& mS) ^^^ (sm2 &&& mA)
  let sqV := xselW mQ qh2 qhS
  let sbV := (bout &&& mS) ^^^ (bin &&& mA)
  let scV := (cin &&& mS) ^^^ (cout &&& mA)
  let qSelIx := (qix &&& mA) ^^^ (du2 &&& (mQ ^^^ mS))
  let qSelV := qv &&& mA
  memSetDyn (memSetDyn (memSetDyn (memSetDyn (memSetDyn acc
    wSelIx.toNat wSelV) sq.toNat sqV) sb.toNat sbV) sc.toNat scV)
    qSelIx.toNat qSelV

/-- One digit's inner loop: the `trips`-fold of `kdTripStep` at a fixed
    outer trip index. -/
def kdInner {NW NV : Nat} (vp : Fin NV → BitVec 64)
    (vnW qnW dinv jdW : BitVec 64) (trips : Nat)
    (acc : Fin NW → BitVec 64) : Fin NW → BitVec 64 :=
  (List.range trips).foldl
    (fun a t => kdTripStep vp vnW qnW dinv a jdW (BitVec.ofNat 64 t)) acc

/-- The identification of one digit's trip fold with the exact digit step,
    on the observable region (window and quotient cells), under the
    normalisation preconditions: `vn ≥ 2`, the divisor's top limb has bit 63
    set, `dinv` its Möller–Granlund reciprocal, and the digit's window below
    `D · 2^64` (the `kdFold_val` invariant, which also bounds the window's
    top limb by the divisor's). Stated here; its proof composes Knuth
    Theorem B (`Mpn.QhatBound`) with the limb-level digit correctness
    (`Mpn.DivRemKnuth.submulAddBackDigit_spec`). -/
def KdDigitAgrees : Prop :=
  ∀ (NW NV : Nat) (vp : Fin NV → BitVec 64) (vn qn jd : Nat)
    (dinv : BitVec 64) (acc : Fin NW → BitVec 64),
    2 ≤ vn → jd < qn → 2 * qn + vn + 5 ≤ NW → vn ≤ NV →
    2 ^ 63 ≤ (memGetDyn vp (vn - 1)).toNat →
    dinv = preinvOf (memGetDyn vp (vn - 1)) →
    bignumVal (segCells acc (qn - 1 - jd) (vn + 1))
        < bignumVal (cells vp vn) * 2 ^ 64 →
    ∀ i : Nat, i < 2 * qn + vn →
      memGetDyn (kdInner vp (BitVec.ofNat 64 vn) (BitVec.ofNat 64 qn) dinv
          (BitVec.ofNat 64 jd) (2 * vn + 3) acc) i
        = memGetDyn (kdDigitStep vp vn (qn + vn) acc (qn - 1 - jd)) i

/-! ## 4. The loop bodies as covered `LowCT`

The inner body runs over the catCryptDialect context
`Gbody = [wp : .memref NW, t : .sword 64, jd : .sword 64, vp : .memref NV,
vn : .sword 64, qn : .sword 64, dinv : .sword 64]` — the accumulator array,
the inner loop index, the outer loop index, then the four invariants. All
arithmetic is in the `srcClean` `SExpr` fragment (`SMul`, `SMulHiU`, `SAdd`,
`SSub`, `SAnd`, `SXor`, `SShr`), so `translateDialectControl` covers it. -/

/-- Word count of the work array in the denotation model: window, quotient
    and scratch for `qn = vn = 4` (`2·4 + 4 + 5`). The rendered SIB accesses
    are byte-offset and size-agnostic; this only bounds the in-Lean model.
    The arithmetic results of §1 and §2 are stated for every `NW` / `NV`. -/
abbrev NW : Nat := 17

/-- Limb count of the divisor array in the denotation model. -/
abbrev NV : Nat := 4

/-- The work-array slot `wp` (`NW` words), the loop accumulator. -/
def wpLoc : Located := ⟨"wp", .TBytes (8 * NW)⟩

/-- The divisor-array slot `vp` (`NV` words), a loop invariant. -/
def vpLoc : Located := ⟨"vp", .TBytes (8 * NV)⟩

/-- The inner trip count of every digit: `vn + vn + 3` — the q̂ trip, the
    `vn + 1` submul trips and the `vn + 1` add-back trips. Recomputed from
    the loop-invariant `vn` each outer pass. -/
def cntBodyLowCT : LowCT :=
  .RScalarSetExpr "cnt" (.SAdd (.SAdd (sv "vn") (sv "vn")) (.SLit 3))

/-- The phase-merged Algorithm D inner body at the runtime indices
    `(jd, t)` — the `LowCT` transcription of `kdTripStep`, command for
    command: the runtime cell offsets, the phase masks, the q̂ phase
    (`preinvStep` on the top two window limbs, the `u₂ = v₁` special case,
    two refinement rounds), the submul and add-back word steps, and the five
    mask-selected stores. -/
def kdBodyLowCT : LowCT := seqAll (
  [ .RScalarSetExpr "j" (.SSub (.SSub (sv "qn") (.SLit 1)) (sv "jd"))
  , .RScalarSetExpr "un1" (.SAdd (sv "qn") (sv "vn"))
  , .RScalarSetExpr "sqx" (.SAdd (sv "un1") (sv "qn"))
  , .RScalarSetExpr "sbx" (.SAdd (sv "sqx") (.SLit 1))
  , .RScalarSetExpr "scx" (.SAdd (sv "sqx") (.SLit 2))
  , .RScalarSetExpr "dux" (.SAdd (sv "sqx") (.SLit 3))
  , .RScalarSetExpr "du2x" (.SAdd (sv "sqx") (.SLit 4)) ]
  ++ ltuCmds "pQ" (sv "t") (.SLit 1)
  ++ [ .RScalarSetExpr "vn2" (.SAdd (sv "vn") (.SLit 2)) ]
  ++ ltuCmds "pSr" (sv "t") (sv "vn2")
  ++ [ .RScalarSetExpr "pQn" (.SXor (sv "pQ") (.SLit 1))
  , .RScalarSetExpr "pS" (.SAnd (sv "pSr") (sv "pQn"))
  , .RScalarSetExpr "pA" (.SXor (sv "pSr") (.SLit 1))
  , .RScalarSetExpr "mQ" (.SSub (.SLit 0) (sv "pQ"))
  , .RScalarSetExpr "mS" (.SSub (.SLit 0) (sv "pS"))
  , .RScalarSetExpr "mA" (.SSub (.SLit 0) (sv "pA"))
  -- q̂ phase: window and divisor top limbs
  , .RScalarSetExpr "jvn" (.SAdd (sv "j") (sv "vn"))
  , .RScalarSetExpr "jv1" (.SSub (sv "jvn") (.SLit 1))
  , .RScalarSetExpr "jv2" (.SSub (sv "jvn") (.SLit 2))
  , .RArrLoad ⟨"u2", .TU64⟩ wpLoc "jvn"
  , .RArrLoad ⟨"u1", .TU64⟩ wpLoc "jv1"
  , .RArrLoad ⟨"u0", .TU64⟩ wpLoc "jv2"
  , .RScalarSetExpr "v1x" (.SSub (sv "vn") (.SLit 1))
  , .RScalarSetExpr "v2x" (.SSub (sv "vn") (.SLit 2))
  , .RArrLoad ⟨"d1", .TU64⟩ vpLoc "v1x"
  , .RArrLoad ⟨"d2", .TU64⟩ vpLoc "v2x"
  -- preinvStep dinv d1 (hi := u2) (lo := u1)
  , .RScalarSetExpr "ql" (.SMul (sv "dinv") (sv "u2"))
  , .RScalarSetExpr "qh" (.SMulHiU (sv "dinv") (sv "u2"))
  , .RScalarSetExpr "qla" (.SAdd (sv "ql") (sv "u1")) ]
  ++ ltuCmds "c0" (sv "qla") (sv "ql")
  ++ [ .RScalarSetExpr "u2p" (.SAdd (sv "u2") (.SLit 1))
  , .RScalarSetExpr "qhb" (.SAdd (.SAdd (sv "qh") (sv "u2p")) (sv "c0"))
  , .RScalarSetExpr "pp" (.SMul (sv "qhb") (sv "d1"))
  , .RScalarSetExpr "rr" (.SSub (sv "u1") (sv "pp")) ]
  ++ ltuCmds "c1" (sv "qla") (sv "rr")
  ++ [ .RScalarSetExpr "m1" (.SAdd (notE (sv "c1")) (.SLit 1))
  , .RScalarSetExpr "qhc" (.SAdd (sv "qhb") (sv "m1"))
  , .RScalarSetExpr "ra" (.SAdd (sv "rr") (.SAnd (sv "m1") (sv "d1"))) ]
  ++ ltuCmds "c2" (sv "ra") (sv "d1")
  ++ [ .RScalarSetExpr "c3" (.SXor (sv "c2") (.SLit 1))
  , .RScalarSetExpr "m3" (.SAdd (notE (sv "c3")) (.SLit 1))
  , .RScalarSetExpr "q0" (.SAdd (sv "qhc") (sv "c3"))
  , .RScalarSetExpr "r0" (.SSub (sv "ra") (.SAnd (sv "m3") (sv "d1"))) ]
  -- the u2 = d1 special case: q̂ = 2^64 - 1, r̂ = u1 + d1 with 65th bit rc0
  ++ ltuCmds "pe" (sv "u2") (sv "d1")
  ++ [ .RScalarSetExpr "peN" (.SXor (sv "pe") (.SLit 1))
  , .RScalarSetExpr "meq" (.SSub (.SLit 0) (sv "peN"))
  , .RScalarSetExpr "rsp" (.SAdd (sv "u1") (sv "d1")) ]
  ++ ltuCmds "rcs" (sv "rsp") (sv "u1")
  ++ [ .RScalarSetExpr "rc0" (.SAnd (sv "rcs") (sv "peN"))
  , .RScalarSetExpr "qh0"
      (.SXor (sv "q0") (.SAnd (.SXor (.SLit ones) (sv "q0")) (sv "meq")))
  , .RScalarSetExpr "rh0"
      (.SXor (sv "r0") (.SAnd (.SXor (sv "rsp") (sv "r0")) (sv "meq")))
  -- refinement round 1
  , .RScalarSetExpr "lo1" (.SMul (sv "qh0") (sv "d2")) ]
  ++ ltuCmds "b11" (sv "u0") (sv "lo1")
  ++ [ .RScalarSetExpr "hi1" (.SMulHiU (sv "qh0") (sv "d2"))
  , .RScalarSetExpr "tt1" (.SSub (sv "rh0") (sv "hi1")) ]
  ++ ltuCmds "b21" (sv "rh0") (sv "hi1")
  ++ ltuCmds "b31" (sv "tt1") (sv "b11")
  ++ [ .RScalarSetExpr "gt1" (.SXor (sv "b21") (sv "b31"))
  , .RScalarSetExpr "rcn1" (.SXor (sv "rc0") (.SLit 1))
  , .RScalarSetExpr "do1" (.SAnd (sv "gt1") (sv "rcn1"))
  , .RScalarSetExpr "md1" (.SSub (.SLit 0) (sv "do1"))
  , .RScalarSetExpr "qh1" (.SSub (sv "qh0") (sv "do1"))
  , .RScalarSetExpr "rh1" (.SAdd (sv "rh0") (.SAnd (sv "d1") (sv "md1"))) ]
  ++ ltuCmds "cch1" (sv "rh1") (sv "rh0")
  ++ [ .RScalarSetExpr "cc1" (.SAnd (sv "cch1") (sv "do1"))
  , .RScalarSetExpr "rc1" (.SXor (sv "rc0") (sv "cc1"))
  -- refinement round 2 (only its q̂ output is live)
  , .RScalarSetExpr "lo2" (.SMul (sv "qh1") (sv "d2")) ]
  ++ ltuCmds "b12" (sv "u0") (sv "lo2")
  ++ [ .RScalarSetExpr "hi2" (.SMulHiU (sv "qh1") (sv "d2"))
  , .RScalarSetExpr "tt2" (.SSub (sv "rh1") (sv "hi2")) ]
  ++ ltuCmds "b22" (sv "rh1") (sv "hi2")
  ++ ltuCmds "b32" (sv "tt2") (sv "b12")
  ++ [ .RScalarSetExpr "gt2" (.SXor (sv "b22") (sv "b32"))
  , .RScalarSetExpr "rcn2" (.SXor (sv "rc1") (.SLit 1))
  , .RScalarSetExpr "do2" (.SAnd (sv "gt2") (sv "rcn2"))
  , .RScalarSetExpr "qh2" (.SSub (sv "qh1") (sv "do2"))
  -- submul phase
  , .RScalarSetExpr "iS" (.SSub (sv "t") (.SLit 1))
  , .RScalarSetExpr "vn1" (.SAdd (sv "vn") (.SLit 1)) ]
  ++ ltuCmds "csx" (sv "iS") (sv "vn1")
  ++ [ .RScalarSetExpr "mcs" (.SSub (.SLit 0) (sv "csx"))
  , .RScalarSetExpr "iScl" (.SAnd (sv "iS") (sv "mcs")) ]
  ++ ltuCmds "inS" (sv "iS") (sv "vn")
  ++ [ .RScalarSetExpr "mv" (.SSub (.SLit 0) (sv "inS"))
  , .RScalarSetExpr "ivx" (.SAnd (sv "iS") (sv "mv"))
  , .RArrLoad ⟨"vld", .TU64⟩ vpLoc "ivx"
  , .RScalarSetExpr "vi" (.SAnd (sv "vld") (sv "mv"))
  , .RArrLoad ⟨"qhS", .TU64⟩ wpLoc "sqx"
  , .RArrLoad ⟨"bin", .TU64⟩ wpLoc "sbx"
  , .RScalarSetExpr "wix" (.SAdd (sv "j") (sv "iScl"))
  , .RArrLoad ⟨"wcell", .TU64⟩ wpLoc "wix"
  , .RScalarSetExpr "plo" (.SMul (sv "qhS") (sv "vi"))
  , .RScalarSetExpr "phi" (.SMulHiU (sv "qhS") (sv "vi"))
  , .RScalarSetExpr "t1" (.SSub (sv "wcell") (sv "bin")) ]
  ++ ltuCmds "b1s" (sv "wcell") (sv "bin")
  ++ [ .RScalarSetExpr "t2" (.SSub (sv "t1") (sv "plo")) ]
  ++ ltuCmds "b2s" (sv "t1") (sv "plo")
  ++ [ .RScalarSetExpr "bout" (.SAdd (.SAdd (sv "phi") (sv "b1s")) (sv "b2s"))
  -- add-back phase
  , .RScalarSetExpr "iA" (.SSub (sv "t") (sv "vn2")) ]
  ++ ltuCmds "cax" (sv "iA") (sv "vn1")
  ++ [ .RScalarSetExpr "mca" (.SSub (.SLit 0) (sv "cax"))
  , .RScalarSetExpr "iAcl" (.SAnd (sv "iA") (sv "mca")) ]
  ++ ltuCmds "inA" (sv "iA") (sv "vn")
  ++ [ .RScalarSetExpr "mva" (.SSub (.SLit 0) (sv "inA"))
  , .RScalarSetExpr "iax" (.SAnd (sv "iA") (sv "mva"))
  , .RArrLoad ⟨"ald", .TU64⟩ vpLoc "iax"
  , .RScalarSetExpr "va" (.SAnd (sv "ald") (sv "mva")) ]
  ++ ltuCmds "bnz" (.SLit 0) (sv "bin")
  ++ [ .RScalarSetExpr "mB" (.SSub (.SLit 0) (sv "bnz"))
  , .RScalarSetExpr "av" (.SAnd (sv "va") (sv "mB"))
  , .RArrLoad ⟨"cin", .TU64⟩ wpLoc "scx"
  , .RScalarSetExpr "aix" (.SAdd (sv "j") (sv "iAcl"))
  , .RArrLoad ⟨"acell", .TU64⟩ wpLoc "aix"
  , .RScalarSetExpr "sm1" (.SAdd (sv "acell") (sv "av")) ]
  ++ ltuCmds "c1a" (sv "sm1") (sv "acell")
  ++ [ .RScalarSetExpr "sm2" (.SAdd (sv "sm1") (sv "cin")) ]
  ++ ltuCmds "c2a" (sv "sm2") (sv "sm1")
  ++ [ .RScalarSetExpr "cout" (.SAdd (sv "c1a") (sv "c2a"))
  , .RScalarSetExpr "qv" (.SSub (sv "qhS") (sv "bnz"))
  , .RScalarSetExpr "qix" (.SAdd (sv "un1") (sv "j"))
  -- mask-selected stores (window, q̂, borrow, carry, quotient)
  , .RScalarSetExpr "wSelIx"
      (.SXor (.SXor (.SAnd (sv "dux") (sv "mQ")) (.SAnd (sv "wix") (sv "mS")))
        (.SAnd (sv "aix") (sv "mA")))
  , .RScalarSetExpr "wSelV"
      (.SXor (.SAnd (sv "t2") (sv "mS")) (.SAnd (sv "sm2") (sv "mA")))
  , .RArrStore wpLoc "wSelIx" ⟨"wSelV", .TU64⟩
  , .RScalarSetExpr "sqV"
      (.SXor (sv "qhS") (.SAnd (.SXor (sv "qh2") (sv "qhS")) (sv "mQ")))
  , .RArrStore wpLoc "sqx" ⟨"sqV", .TU64⟩
  , .RScalarSetExpr "sbV"
      (.SXor (.SAnd (sv "bout") (sv "mS")) (.SAnd (sv "bin") (sv "mA")))
  , .RArrStore wpLoc "sbx" ⟨"sbV", .TU64⟩
  , .RScalarSetExpr "scV"
      (.SXor (.SAnd (sv "cin") (sv "mS")) (.SAnd (sv "cout") (sv "mA")))
  , .RArrStore wpLoc "scx" ⟨"scV", .TU64⟩
  , .RScalarSetExpr "mQS" (.SXor (sv "mQ") (sv "mS"))
  , .RScalarSetExpr "qSelIx"
      (.SXor (.SAnd (sv "qix") (sv "mA")) (.SAnd (sv "du2x") (sv "mQS")))
  , .RScalarSetExpr "qSelV" (.SAnd (sv "qv") (sv "mA"))
  , .RArrStore wpLoc "qSelIx" ⟨"qSelV", .TU64⟩ ])

/-- The loop invariants: the divisor array and the three runtime scalars. -/
def Ginv : Ctx := [.memref NV, .sword 64, .sword 64, .sword 64]

/-- The inner-body context: accumulator, inner index, outer index,
    invariants. -/
def Gbody : Ctx := .memref NW :: .sword 64 :: .sword 64 :: Ginv

/-- The inner-count-body context: outer index, invariants. -/
def Gcount : Ctx := .sword 64 :: Ginv

/-- The inner-body `VarMap`: `dinv` bound deepest, then `qn`, `vn`, `vp`,
    `jd`, `t`, and `wp` at `.here`. -/
def vmBody : VarMap Gbody :=
  ((((((VarMap.empty.bind (t := .sword 64) "dinv").bind
      (t := .sword 64) "qn").bind
      (t := .sword 64) "vn").bind
      (t := .memref NV) "vp").bind
      (t := .sword 64) "jd").bind
      (t := .sword 64) "t").bind (t := .memref NW) "wp"

/-- The inner-count-body `VarMap`. -/
def vmCount : VarMap Gcount :=
  ((((VarMap.empty.bind (t := .sword 64) "dinv").bind
      (t := .sword 64) "qn").bind
      (t := .sword 64) "vn").bind
      (t := .memref NV) "vp").bind (t := .sword 64) "jd"

/-! ## 5. The nested runtime-trip loop program

Outer argument context `[dinv, vn, qn, vp, wp]` (newest first), routing
`wp → RDI`, `vp → RSI`, `qn → RDX`, `vn → RCX`, `dinv → R8`. -/

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The work-array jasmin type. -/
abbrev AW : JasminTy := .stackArr 64 NW

/-- The divisor-array jasmin type. -/
abbrev AV : JasminTy := .stackArr 64 NV

/-- The kernel's outer argument context, newest first. -/
abbrev Gouter : Ctxt jasminDialect := [r64, r64, r64, AV, AW]

/-- The runtime outer trip count `qn` (RDX). -/
def kdOuterCount : Ctxt.Var Gouter r64 := .there (.there .here)

/-- The accumulator seed: the work array `wp` (RDI). -/
def kdInit : Ctxt.Var Gouter AW := .there (.there (.there (.there .here)))

/-- The loop invariants: `vp` (RSI), `vn` (RCX), `qn` (RDX) and `dinv`
    (R8). -/
def kdInvs : HVector (fun ty => Ctxt.Var Gouter ty) [AV, r64, r64, r64] :=
  .cons (.there (.there (.there .here)))
    (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here .nil)))

/-- The front-compiled nested runtime-trip `mpn_div_qr`: one inner body copy
    behind two `jne` back-edges, the outer trip counter seeded from the
    runtime `qn` register, the inner trip recomputed as `2·vn + 3` each
    outer pass, the work array threaded as the loop accumulator and
    `vp`/`vn`/`qn`/`dinv` as loop invariants. `none` if either front
    declines. -/
def kdProgOpt : Option (ComL Gouter AW) :=
  Dialects.FrontRoutePlan.compileNested (Γouter := Gouter) (accCTy := .memref NW)
    (invCTys := Ginv) .plain
    vmCount "cnt" cntBodyLowCT
    vmBody "wp" kdBodyLowCT
    kdOuterCount kdInit kdInvs

/-- **The emitted nest's denotation is the `JLoopBodyN.nestedDenote` double
    fold of the front bodies.** Whenever the front compiles `cntBodyLowCT`
    to `innerCount` and `kdBodyLowCT` to `innerUpdate`, the program's
    denotation at any valuation is the outer fold over `qn` digits of the
    inner fold over the recomputed trip count, seeded by the `wp` argument
    and threading the invariants. The instance of
    `rolledForLoopNRtNested_denote` at this kernel. -/
theorem kdProg_denote
    {innerCount : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.sword 64 :: Ginv))
      (CryptoToJasminCom.mapTy (CryptoTy.sword 64))}
    {innerUpdate : Com jasminDialect
      (CryptoToJasminCom.mapCtx
        (CryptoTy.memref NW :: .sword 64 :: .sword 64 :: Ginv))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NW))}
    (hcnt : Dialects.TranslateDialectRolledLoop.frontLoopBodyJ
      (accCTy := .sword 64) (Γbody := .sword 64 :: Ginv)
      vmCount "cnt" cntBodyLowCT = some innerCount)
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJ
      (accCTy := .memref NW)
      (Γbody := CryptoTy.memref NW :: .sword 64 :: .sword 64 :: Ginv)
      vmBody "wp" kdBodyLowCT = some innerUpdate)
    (V : Ctxt.Valuation Gouter) :
    kdProgOpt.map (fun c => ComL.denote c V)
      = some (JLoopBodyN.nestedDenote innerCount innerUpdate
          (kdOuterCount.lookup V).toNat (Expr.lookupArgs kdInvs V)
          (kdInit.lookup V)) :=
  rolledForLoopNRtNested_denote vmCount "cnt" cntBodyLowCT vmBody "wp" kdBodyLowCT
    kdOuterCount kdInit kdInvs hcnt hupd V

/-! ## 6. The owned `Lprog` and the rendered `.s` -/

/-- The rolled, owned-RA 5-argument-ABI `Lprog` for the runtime-trip
    `mpn_div_qr` under the C symbol `fname`
    (`RDI = wp`, `RSI = vp`, `RDX = qn`, `RCX = vn`, `R8 = dinv`).

    The `MULXHI` high-word binding the front emits for `SMulHiU` is coalesced
    with its paired low `MUL` into the printer's two-output `mulx` by
    `FheMontMulEmit.fuseMulHiLprog` in its `saveRdx` looped-body mode. -/
def kdLprogOpt (fname : String) : Option Lprog :=
  kdProgOpt.map (fun c =>
    FheMontMulEmit.fuseMulHiLprog
      (ComL.toLprogPhysAbi c fname (argName 0) [argName 1]
        (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX", "R8"]
        [64, 64, 64, 64, 64])
      (saveRdx := true))

/-- The owned AT&T `.s` text for the runtime-trip `mpn_div_qr`. -/
def kdAsmOpt (fname : String) : Option String :=
  (kdLprogOpt fname).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

/-- The 5-argument-ABI physical body of the front-compiled nested loop. -/
def kdPhysBodyOpt : Option Lcmd :=
  kdProgOpt.map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX", "R8"]
      [64, 64, 64, 64, 64]).lfd_body)

/-! ## 7. Emit driver and structural gates

The render is written while this module elaborates, so `lake` produces it
from this file and no separate driver or Makefile rule carries the
dependency. The front-acceptance, loop-spine, back-edge and render gates run
in the same `IO` action and throw — failing elaboration — when violated. -/

/-- Write the owned-backend `.s` for the runtime-trip `mpn_div_qr_preinv`
    into the `bench/mpn_divqr_front_compare/gen_com` harness directory,
    after checking: the front accepts both bodies; the spine is
    `ComL.forLoopNRtNested`; the physical body carries exactly two
    bottom-test back-edges; the rendered text is nonempty, `UNHANDLED`-free
    and carries the fused widening multiply. -/
def emitMain : IO Unit := do
  let dir := "bench/mpn_divqr_front_compare/gen_com"
  IO.FS.createDirAll dir
  match kdProgOpt with
  | none => throw (IO.userError "the nested runtime-loop front declined mpn_div_qr")
  | some c =>
      let spineOk := match c with
        | .forLoopNRtNested _ _ _ _ _ _ => true
        | _ => false
      unless spineOk do
        throw (IO.userError "mpn_div_qr spine is not ComL.forLoopNRtNested")
      match kdPhysBodyOpt with
      | none => throw (IO.userError "mpn_div_qr physical body missing")
      | some body =>
          let backEdges := (body.filter (fun i => match i.li_i with
            | .Lcond (.reg "NZ") _ => true | _ => false)).length
          unless backEdges == 2 do
            throw (IO.userError
              s!"mpn_div_qr back-edge count {backEdges}, expected 2")
      match kdAsmOpt "mpn_div_qr_preinv" with
      | none => throw (IO.userError "mpn_div_qr render missing")
      | some s =>
          unless s.length > 0 do
            throw (IO.userError "mpn_div_qr render is empty")
          if strContains s "UNHANDLED" then
            throw (IO.userError "mpn_div_qr render carries UNHANDLED")
          unless strContains s "mulx" do
            throw (IO.userError "mpn_div_qr render lacks the fused mulx")
          IO.FS.writeFile (dir ++ "/mpn_div_qr_preinv_owned.s") s
          IO.println
            "WROTE bench/mpn_divqr_front_compare/gen_com/mpn_div_qr_preinv_owned.s"

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivQrFrontEmit
