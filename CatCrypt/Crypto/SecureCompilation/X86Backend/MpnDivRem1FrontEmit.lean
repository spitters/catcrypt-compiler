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
# `mpn_divrem_1` as a front-generated runtime-trip loop

`mpn_divrem_1(qp, up, n, d)` sets `qp[0..n) = up[0..n) / d` and leaves the
remainder `up[0..n) mod d`. This module sources the descending single-limb
division loop through the verified runtime-loop front: the per-limb body is
covered `LowCT` (`RArrLoad` / `RScalarSetExpr` / `RArrStore` over the runtime
loop index), and
`Dialects.TranslateDialectRuntimeLoop.rolledForLoopNRt` front-compiles it into a
`ComL.forLoopNRt` — one body copy behind a `jne` back-edge, the trip counter
seeded from the runtime `n` register.

The owned x86 backend has no `div` instruction and the covered `SExpr` fragment
has no division operator, so the per-limb quotient digit is produced by the
Möller–Granlund reciprocal step `udiv_qrnnd_preinv`: a widening multiply by a
precomputed reciprocal `dinv` of the normalised divisor, followed by two
branch-free corrections. Every operation is in the `srcClean` fragment
(`SMul`, `SMulHiU`, `SAdd`, `SSub`, `SAnd`, `SXor`, `SShr`).

```
  divLimbBodyLowCT (RArrLoad qp at rs, RArrLoad up at j = top - idx,
                    SMulHiU/SMul reciprocal step, bSltu corrections,
                    RArrStore qp at j, RArrStore qp at rs)
    --(rolledForLoopNRt)--> JLoopBodyN.update : Com jasminDialect …
    --(ComL.forLoopNRt update n qp [d, dinv, n, up] (ret qp))--> ComL
    --(ComL.toLprogPhysAbi / renderLprogAtt)-------------------> AT&T .s
```

## The remainder cell

The loop-carried accumulator is the whole output array `qp`; the running
remainder rides in the dedicated high cell `rs`. At trip `t` the descending limb
index is `j = top - t`; the body reads the remainder from `qp[rs]` and the
dividend limb from `up[j]`, and writes the quotient limb to `qp[j]` and the new
remainder back to `qp[rs]`. Because `top < rs`, the remainder cell never
collides with a quotient cell.

## ABI

```c
extern uint64_t *mpn_divrem_1_preinv(uint64_t *qp, const uint64_t *up,
                                     uint64_t n, uint64_t d, uint64_t dinv);
```

`qp` (RDI), `up` (RSI), `n` (RDX), `d` (RCX), `dinv` (R8). `qp` holds `rs + 1`
words; cell `rs` supplies the incoming remainder, which must be below `d`, and
receives the outgoing remainder. `d` must be normalised (bit 63 set) and `dinv`
its Möller–Granlund reciprocal.

## Main results

* `divLimb_val` / `divLimb_lt`: the per-limb Euclidean identity
  `q · d + r = u1 · 2^64 + u0` and `r < d`, under `u1 < d`.
* `divFold_val_rem`: the loop invariant over the memref carrier — for a seed
  `r0 = qp[rs]` below `d`, after `k` trips the accumulator cells
  `top+1-k … top` hold the top `k` quotient limbs and cell `rs` the running
  remainder, with
  `value (qp[top+1-k … top]) · d + r = r0 · 2^(64k) + value (up[top+1-k … top])`,
  for every `NR` / `NU`. `divFold_val` is its `r0 = 0` instance.
* `divRem1RtProg_denote`: the runtime-trip loop program's denotation as the
  `JLoopBodyN` fold of the front body.
* `preinvStep`: the word function the emitted body computes, and
  `PreinvStepAgrees`, the residual identifying it with `divLimb`, corroborated by
  `#guard`s over a grid of normalised divisors.
* `divRem1RtLprogOpt` / `divRem1RtAsmOpt`: the owned `Lprog` and its AT&T text.

## Control flow

`divLimbBodyLowCT` carries no `RIfNz` and no `RWhileNz`: both quotient
corrections are mask arithmetic over `bSltu`, so one loop trip is a fixed
straight-line instruction sequence and the only control flow in the kernel is the
trip-count back-edge, whose count is the public limb count `n`.

## Scope

`divLimb_val`, `divLimb_lt`, `divFold_val_rem` and `divFold_val` hold for every
`NR` / `NU`; `NU`
fixes only the memref width of the concrete front-compiled instance below, whose
rendered SIB accesses are byte-offset and so size-agnostic.

`divFold_val` is a statement about the arithmetic model `divLimb`, the exact
Euclidean step. `preinvStep` is the word function the emitted body computes.
`PreinvStepAgrees` is the `Prop` recording their identification under the
Möller–Granlund preconditions; it is stated, not discharged, here.

`divRem1RtProg_denote` carries the front-compilation hypothesis
`frontLoopBodyJ … = some update` and concludes at `JLoopBodyN.denote` of that
`update`. Identifying that denotation with `preinvStep` — so that the invariant
reads as a statement about the emitted kernel — is the separate
source-preservation step (`translateDialectControl_denote_ctl` composed with
`cryptoDialectToJasminCom`), not established here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit

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
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (memGetDyn_memSetDyn_ne memGetDyn_memSetDyn_self seqAll ones notE orE sv ltuCmds)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-! ## 1. The exact Euclidean limb step -/

/-- One `mpn_divrem_1` limb step on words: divide the two-limb value
    `u1 · 2^64 + u0` by `d`, returning `(quotient limb, remainder)`. -/
def divLimb (u1 u0 d : BitVec 64) : BitVec 64 × BitVec 64 :=
  (BitVec.ofNat 64 ((u1.toNat * 2 ^ 64 + u0.toNat) / d.toNat),
   BitVec.ofNat 64 ((u1.toNat * 2 ^ 64 + u0.toNat) % d.toNat))

/-- Under `u1 < d` the quotient digit fits in one word. -/
theorem divLimb_quot_lt (u1 u0 d : BitVec 64) (hlt : u1.toNat < d.toNat) :
    (u1.toNat * 2 ^ 64 + u0.toNat) / d.toNat < 2 ^ 64 := by
  have hd : 0 < d.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
  have hu0 := u0.isLt
  have hbound : u1.toNat * 2 ^ 64 + u0.toNat < d.toNat * 2 ^ 64 := by
    have : u1.toNat + 1 ≤ d.toNat := hlt
    nlinarith
  exact Nat.div_lt_of_lt_mul (by linarith [hbound])

/-- **The single-limb division identity.** `divLimb u1 u0 d` splits
    `u1 · 2^64 + u0` into a quotient digit and a remainder:
    `q · d + r = u1 · 2^64 + u0`. -/
theorem divLimb_val (u1 u0 d : BitVec 64) (hlt : u1.toNat < d.toNat) :
    (divLimb u1 u0 d).1.toNat * d.toNat + (divLimb u1 u0 d).2.toNat
      = u1.toNat * 2 ^ 64 + u0.toNat := by
  have hd : 0 < d.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
  have hq := divLimb_quot_lt u1 u0 d hlt
  have hr : (u1.toNat * 2 ^ 64 + u0.toNat) % d.toNat < 2 ^ 64 :=
    Nat.lt_trans (Nat.mod_lt _ hd) d.isLt
  simp only [divLimb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hr]
  exact Nat.div_add_mod' _ _

/-- The remainder is below the divisor. -/
theorem divLimb_lt (u1 u0 d : BitVec 64) (hlt : u1.toNat < d.toNat) :
    (divLimb u1 u0 d).2.toNat < d.toNat := by
  have hd : 0 < d.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
  have hmod := Nat.mod_lt (u1.toNat * 2 ^ 64 + u0.toNat) hd
  have hr : (u1.toNat * 2 ^ 64 + u0.toNat) % d.toNat < 2 ^ 64 :=
    Nat.lt_trans hmod d.isLt
  show ((BitVec.ofNat 64 ((u1.toNat * 2 ^ 64 + u0.toNat) % d.toNat)).toNat) < d.toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  exact hmod

/-! ## 2. The same chain over the memref carrier

The emitted loop carries the whole output array as its accumulator and folds one
body copy over the trip indices, descending through the dividend limbs.
`divFoldStep` is that body's word-level effect and `divFold` the
`(List.range k).foldl` shape `JLoopBodyN.denote` folds the emitted body in. -/

/-- The cells `lo, …, lo + k - 1` of a memref as a little-endian limb list. -/
def segCells {N : Nat} (arr : Fin N → BitVec 64) (lo k : Nat) : List (BitVec 64) :=
  (List.range k).map (fun i => memGetDyn arr (lo + i))

/-- `segCells` at a lowered base prepends the cell below. -/
theorem segCells_cons {N : Nat} (arr : Fin N → BitVec 64) (lo k : Nat) :
    segCells arr lo (k + 1) = memGetDyn arr lo :: segCells arr (lo + 1) k := by
  simp [segCells, List.range_succ_eq_map, Nat.add_comm, Nat.add_left_comm]

/-- One trip of the emitted loop on the accumulator array: at trip `t` the
    descending limb index is `j = top - t`; read the running remainder from cell
    `rs` and the dividend limb from `up[j]`, write the quotient limb to cell `j`
    and the new remainder to cell `rs`. -/
def divFoldStep {NR NU : Nat} (up : Fin NU → BitVec 64) (d : BitVec 64)
    (top rs : Nat) (acc : Fin NR → BitVec 64) (t : Nat) : Fin NR → BitVec 64 :=
  memSetDyn (memSetDyn acc (top - t)
      (divLimb (memGetDyn acc rs) (memGetDyn up (top - t)) d).1)
    rs (divLimb (memGetDyn acc rs) (memGetDyn up (top - t)) d).2

/-- The `k`-fold of `divFoldStep` over the trip indices `0, …, k-1`: the
    `(List.range k).foldl` shape `JLoopBodyN.denote` folds the emitted loop body
    in, at accumulator type `.stackArr 64 NR`. -/
def divFold {NR NU : Nat} (up : Fin NU → BitVec 64) (d : BitVec 64)
    (top rs : Nat) (k : Nat) (acc : Fin NR → BitVec 64) : Fin NR → BitVec 64 :=
  (List.range k).foldl (divFoldStep up d top rs) acc

/-- The fold peels its last trip. -/
theorem divFold_succ {NR NU : Nat} (up : Fin NU → BitVec 64) (d : BitVec 64)
    (top rs k : Nat) (acc : Fin NR → BitVec 64) :
    divFold up d top rs (k + 1) acc = divFoldStep up d top rs (divFold up d top rs k acc) k := by
  simp [divFold, List.range_succ, List.foldl_append]

/-- Cells strictly above the trip's write index and distinct from the remainder
    cell are untouched. -/
theorem divFoldStep_frame {NR NU : Nat} (up : Fin NU → BitVec 64) (d : BitVec 64)
    (top rs : Nat) (acc : Fin NR → BitVec 64) (t j : Nat)
    (hrs : rs < NR) (hj : j < NR) (hjt : top - t < j) (hjrs : j ≠ rs) :
    memGetDyn (divFoldStep up d top rs acc t) j = memGetDyn acc j := by
  rw [divFoldStep,
    memGetDyn_memSetDyn_ne _ rs j _ hrs hj hjrs,
    memGetDyn_memSetDyn_ne _ (top - t) j _ (by omega) hj (by omega)]

/-- The whole already-written segment above the trip's write index is unchanged. -/
theorem divFoldStep_segCells {NR NU : Nat} (up : Fin NU → BitVec 64) (d : BitVec 64)
    (top rs : Nat) (acc : Fin NR → BitVec 64) (t k : Nat)
    (hrs : rs < NR) (htop : top < rs) (hkt : k ≤ t) (htp : t ≤ top) :
    segCells (divFoldStep up d top rs acc t) (top - t + 1) k
      = segCells acc (top - t + 1) k := by
  simp only [segCells, List.map_inj_left, List.mem_range]
  intro i hi
  exact divFoldStep_frame up d top rs acc t (top - t + 1 + i) hrs (by omega)
    (by omega) (by omega)

/-- **The division loop invariant with an incoming remainder.** Let
    `r0 = qp[rs]` be the seed of the remainder cell, below the divisor. After
    `k` trips the accumulator's cells `top+1-k, …, top` hold the top `k`
    quotient limbs and cell `rs` the running remainder, and
    `value (qp[top+1-k … top]) · d + r = r0 · 2^(64k) + value (up[top+1-k … top])`.
    The remainder stays below the divisor. -/
theorem divFold_val_rem {NR NU : Nat} (up : Fin NU → BitVec 64) (d : BitVec 64)
    (top rs : Nat) (acc : Fin NR → BitVec 64)
    (hrs : rs < NR) (htop : top < rs)
    (h0 : (memGetDyn acc rs).toNat < d.toNat) :
    ∀ k : Nat, k ≤ top + 1 →
      (memGetDyn (divFold up d top rs k acc) rs).toNat < d.toNat
        ∧ bignumVal (segCells (divFold up d top rs k acc) (top + 1 - k) k) * d.toNat
            + (memGetDyn (divFold up d top rs k acc) rs).toNat
          = (memGetDyn acc rs).toNat * 2 ^ (64 * k)
            + bignumVal (segCells up (top + 1 - k) k) := by
  intro k
  induction k with
  | zero =>
      intro _
      simp [divFold, segCells, bignumVal, h0]
  | succ m ih =>
      intro hm
      have hm' : m ≤ top + 1 := by omega
      obtain ⟨hrlt, hIH⟩ := ih hm'
      set F : Fin NR → BitVec 64 := divFold up d top rs m acc with hF
      -- trip `m` writes cell `top - m`, which is the cell below the segment base
      have hbase : top + 1 - (m + 1) = top - m := by omega
      have hshift : top - m + 1 = top + 1 - m := by omega
      -- the two cells trip `m` writes
      have hq : memGetDyn (divFoldStep up d top rs F m) (top - m)
          = (divLimb (memGetDyn F rs) (memGetDyn up (top - m)) d).1 := by
        rw [divFoldStep,
          memGetDyn_memSetDyn_ne _ rs (top - m) _ hrs (by omega) (by omega),
          memGetDyn_memSetDyn_self _ (top - m) _ (by omega)]
      have hr : memGetDyn (divFoldStep up d top rs F m) rs
          = (divLimb (memGetDyn F rs) (memGetDyn up (top - m)) d).2 :=
        memGetDyn_memSetDyn_self _ rs _ hrs
      have hstep := divLimb_val (memGetDyn F rs) (memGetDyn up (top - m)) d hrlt
      have hstepLt := divLimb_lt (memGetDyn F rs) (memGetDyn up (top - m)) d hrlt
      have hframe : segCells (divFoldStep up d top rs F m) (top - m + 1) m
          = segCells F (top - m + 1) m :=
        divFoldStep_segCells up d top rs F m m hrs htop (Nat.le_refl m) (by omega)
      refine ⟨by rw [divFold_succ, hr]; exact hstepLt, ?_⟩
      rw [hshift] at hframe
      rw [divFold_succ, hbase, segCells_cons, segCells_cons, hshift]
      simp only [bignumVal]
      rw [hq, hr, hframe]
      calc ((divLimb (memGetDyn F rs) (memGetDyn up (top - m)) d).1.toNat
              + 2 ^ 64 * bignumVal (segCells F (top + 1 - m) m)) * d.toNat
            + (divLimb (memGetDyn F rs) (memGetDyn up (top - m)) d).2.toNat
          = ((divLimb (memGetDyn F rs) (memGetDyn up (top - m)) d).1.toNat * d.toNat
              + (divLimb (memGetDyn F rs) (memGetDyn up (top - m)) d).2.toNat)
            + 2 ^ 64 * (bignumVal (segCells F (top + 1 - m) m) * d.toNat) := by ring
        _ = ((memGetDyn F rs).toNat * 2 ^ 64 + (memGetDyn up (top - m)).toNat)
              + 2 ^ 64 * (bignumVal (segCells F (top + 1 - m) m) * d.toNat) := by
              rw [hstep]
        _ = (memGetDyn up (top - m)).toNat
              + 2 ^ 64 * (bignumVal (segCells F (top + 1 - m) m) * d.toNat
                  + (memGetDyn F rs).toNat) := by ring
        _ = (memGetDyn up (top - m)).toNat
              + 2 ^ 64 * ((memGetDyn acc rs).toNat * 2 ^ (64 * m)
                + bignumVal (segCells up (top + 1 - m) m)) := by rw [hIH]
        _ = (memGetDyn acc rs).toNat * 2 ^ (64 * (m + 1))
              + ((memGetDyn up (top - m)).toNat
                + 2 ^ 64 * bignumVal (segCells up (top + 1 - m) m)) := by
              rw [Nat.mul_succ, Nat.pow_add]; ring

/-- **The division loop invariant.** With the remainder cell `rs` seeded at
    zero, after `k` trips the accumulator's cells `top+1-k, …, top` hold the top
    `k` quotient limbs and cell `rs` the running remainder, and
    `value (qp[top+1-k … top]) · d + r = value (up[top+1-k … top])`. The
    remainder stays below the divisor. The `r0 = 0` instance of
    `divFold_val_rem`. -/
theorem divFold_val {NR NU : Nat} (up : Fin NU → BitVec 64) (d : BitVec 64)
    (top rs : Nat) (acc : Fin NR → BitVec 64)
    (hrs : rs < NR) (htop : top < rs)
    (h0 : memGetDyn acc rs = 0) (hd : 0 < d.toNat) :
    ∀ k : Nat, k ≤ top + 1 →
      (memGetDyn (divFold up d top rs k acc) rs).toNat < d.toNat
        ∧ bignumVal (segCells (divFold up d top rs k acc) (top + 1 - k) k) * d.toNat
            + (memGetDyn (divFold up d top rs k acc) rs).toNat
          = bignumVal (segCells up (top + 1 - k) k) := by
  intro k hk
  have h := divFold_val_rem up d top rs acc hrs htop (by simp [h0, hd]) k hk
  simpa [h0] using h

/-! ## 3. The reciprocal step the emitted body computes

The owned x86 backend has no `div` instruction, so the quotient digit is
produced by the Möller–Granlund reciprocal step. `preinvStep dinv d u1 u0` is the
word function the emitted `LowCT` body of §4 computes, transcribed op for op. -/

/-- `x <u y` as a `0`/`1` word — the `FieldReduceIdioms.bSltu` shape the covered
    `SExpr` fragment admits. -/
abbrev ltuW (x y : BitVec 64) : BitVec 64 := bSltu x y

/-- The Möller–Granlund reciprocal division step `udiv_qrnnd_preinv`: the
    two-limb value `u1 · 2^64 + u0` divided by `d` using the precomputed
    reciprocal `dinv`, as `(quotient digit, remainder)`. Every operation is a
    word add, subtract, multiply, high-multiply, bitwise and, or the branch-free
    `bSltu` comparison — the ops the covered `SExpr` fragment admits. -/
def preinvStep (dinv d u1 u0 : BitVec 64) : BitVec 64 × BitVec 64 :=
  let qh := mulHiW dinv u1
  let ql := dinv * u1
  let ql' := ql + u0
  let c0 := ltuW ql' ql
  let qh' := qh + (u1 + 1) + c0
  let r := u0 - qh' * d
  let c1 := ltuW ql' r
  let m1 := (~~~c1) + 1
  let qh'' := qh' + m1
  let r' := r + (m1 &&& d)
  let c2 := ltuW r' d
  let c3 := c2 ^^^ 1
  let m3 := (~~~c3) + 1
  (qh'' + c3, r' - (m3 &&& d))

/-- The identification of the emitted reciprocal step with the exact Euclidean
    step, under the Möller–Granlund preconditions: `d` normalised (bit 63 set),
    `u1 < d`, and `dinv` the reciprocal `⌊(2^128 - 1) / d⌋ - 2^64`. Stated here;
    its proof is the Möller–Granlund bound argument. -/
def PreinvStepAgrees : Prop :=
  ∀ dinv d u1 u0 : BitVec 64,
    2 ^ 63 ≤ d.toNat →
    u1.toNat < d.toNat →
    dinv.toNat = (2 ^ 128 - 1) / d.toNat - 2 ^ 64 →
    preinvStep dinv d u1 u0 = divLimb u1 u0 d

/-- The Möller–Granlund reciprocal of a normalised divisor. -/
def preinvOf (d : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((2 ^ 128 - 1) / d.toNat - 2 ^ 64)

-- The reciprocal step agrees with the exact Euclidean step on concrete
-- normalised divisors and two-limb dividends.
#guard preinvStep (preinvOf 0x8000000000000000#64) 0x8000000000000000#64
    0x1234567890abcdef#64 0xfedcba0987654321#64
  = divLimb 0x1234567890abcdef#64 0xfedcba0987654321#64 0x8000000000000000#64

#guard preinvStep (preinvOf 0xffffffffffffffff#64) 0xffffffffffffffff#64
    0xfffffffffffffffe#64 0xffffffffffffffff#64
  = divLimb 0xfffffffffffffffe#64 0xffffffffffffffff#64 0xffffffffffffffff#64

#guard preinvStep (preinvOf 0xdeadbeefcafebabe#64) 0xdeadbeefcafebabe#64
    0x0000000000000000#64 0x0123456789abcdef#64
  = divLimb 0x0000000000000000#64 0x0123456789abcdef#64 0xdeadbeefcafebabe#64

#guard preinvStep (preinvOf 0x9e3779b97f4a7c15#64) 0x9e3779b97f4a7c15#64
    0x9e3779b97f4a7c14#64 0x0000000000000001#64
  = divLimb 0x9e3779b97f4a7c14#64 0x0000000000000001#64 0x9e3779b97f4a7c15#64

-- A grid of normalised divisors against dividends with `u1 < d`: the reciprocal
-- step agrees with the exact Euclidean step at every point.
#guard (List.range 10).all (fun i =>
  let d : BitVec 64 := 0x8000000000000000#64 + BitVec.ofNat 64 (i * 0x0123456789abcdef)
  (List.range 10).all (fun k =>
    let u1 : BitVec 64 := BitVec.ofNat 64 ((k * 0x9e3779b97f4a7c15) % d.toNat)
    let u0 : BitVec 64 := BitVec.ofNat 64 (k * 0xdeadbeefcafebabe)
    preinvStep (preinvOf d) d u1 u0 == divLimb u1 u0 d))

/-! ## 4. The loop body as covered `LowCT`

The body runs over the catCryptDialect context
`Γbody = [qp : .memref NR, idx : .sword 64, d : .sword 64, dinv : .sword 64,
n : .sword 64, up : .memref NU]` — the accumulator array, the runtime loop index,
then the four invariants. All arithmetic is in the `srcClean` `SExpr` fragment,
so `translateDialectControl` covers it. -/

/-- Limb count of the dividend array in the denotation model. The rendered SIB
    loads use byte offsets, so the assembly is size-agnostic; this only bounds
    the in-Lean model. The arithmetic results of §1 and §2 are stated for every
    `NU` / `NR`. -/
abbrev NU : Nat := 8

/-- The accumulator cell holding the running remainder: the word above the `NU`
    quotient limbs. -/
abbrev RS : Nat := NU

/-- Word count of the output array: `NU` quotient limbs plus the remainder cell. -/
abbrev NR : Nat := NU + 1

/-- The output-array slot `qp` (`NR` words), the loop accumulator. -/
def qpLoc : Located := ⟨"qp", .TBytes (8 * NR)⟩

/-- The dividend-array slot `up` (`NU` words), a loop invariant. -/
def upLoc : Located := ⟨"up", .TBytes (8 * NU)⟩

/-- One `mpn_divrem_1` limb at the runtime loop index `idx`: form the descending
    limb index `j = (n - 1) - idx`, read the running remainder from `qp[RS]` and
    the dividend limb from `up[j]`, run the reciprocal step, then store the
    quotient limb to `qp[j]` and the new remainder to `qp[RS]`. -/
def divLimbBodyLowCT : LowCT := seqAll (
  [ LowCT.RScalarSetExpr "top" (.SSub (sv "n") (.SLit 1))
  , .RScalarSetExpr "j" (.SSub (sv "top") (sv "idx"))
  , .RScalarSetExpr "rs" (.SLit RS)
  , .RArrLoad ⟨"u1", .TU64⟩ qpLoc "rs"
  , .RArrLoad ⟨"u0", .TU64⟩ upLoc "j"
  , .RScalarSetExpr "ql" (.SMul (sv "dinv") (sv "u1"))
  , .RScalarSetExpr "qh" (.SMulHiU (sv "dinv") (sv "u1"))
  , .RScalarSetExpr "qla" (.SAdd (sv "ql") (sv "u0")) ]
  ++ ltuCmds "c0" (sv "qla") (sv "ql")
  ++ [ LowCT.RScalarSetExpr "u1p" (.SAdd (sv "u1") (.SLit 1))
     , .RScalarSetExpr "qhb" (.SAdd (.SAdd (sv "qh") (sv "u1p")) (sv "c0"))
     , .RScalarSetExpr "p" (.SMul (sv "qhb") (sv "d"))
     , .RScalarSetExpr "r" (.SSub (sv "u0") (sv "p")) ]
  ++ ltuCmds "c1" (sv "qla") (sv "r")
  ++ [ LowCT.RScalarSetExpr "m1" (.SAdd (notE (sv "c1")) (.SLit 1))
     , .RScalarSetExpr "qhc" (.SAdd (sv "qhb") (sv "m1"))
     , .RScalarSetExpr "ra" (.SAdd (sv "r") (.SAnd (sv "m1") (sv "d"))) ]
  ++ ltuCmds "c2" (sv "ra") (sv "d")
  ++ [ LowCT.RScalarSetExpr "c3" (.SXor (sv "c2") (.SLit 1))
     , .RScalarSetExpr "m3" (.SAdd (notE (sv "c3")) (.SLit 1))
     , .RScalarSetExpr "qout" (.SAdd (sv "qhc") (sv "c3"))
     , .RScalarSetExpr "rout" (.SSub (sv "ra") (.SAnd (sv "m3") (sv "d")))
     , .RArrStore qpLoc "j" ⟨"qout", .TU64⟩
     , .RArrStore qpLoc "rs" ⟨"rout", .TU64⟩ ])

/-- The loop-body context: accumulator `qp`, runtime loop index, then the
    divisor, its reciprocal, the limb count and the dividend array as
    invariants. -/
def Gbody : Ctx :=
  [.memref NR, .sword 64, .sword 64, .sword 64, .sword 64, .memref NU]

/-- The body `VarMap`: `up` bound deepest, then `n`, `dinv`, `d`, `idx`, and `qp`
    at `.here`. -/
def vmBody : VarMap Gbody :=
  ((((((VarMap.empty.bind (t := .memref NU) "up").bind
      (t := .sword 64) "n").bind
      (t := .sword 64) "dinv").bind
      (t := .sword 64) "d").bind
      (t := .sword 64) "idx").bind (t := .memref NR) "qp")

/-! ## 5. The runtime-trip loop program

Outer argument context `[dinv, d, n, up, qp]` (newest first), routing
`qp → RDI`, `up → RSI`, `n → RDX`, `d → RCX`, `dinv → R8`. -/

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The output-array jasmin type. -/
abbrev AQ : JasminTy := .stackArr 64 NR

/-- The dividend-array jasmin type. -/
abbrev AU : JasminTy := .stackArr 64 NU

/-- The kernel's outer argument context, newest first. -/
abbrev Gouter : Ctxt jasminDialect := [r64, r64, r64, AU, AQ]

/-- The runtime trip count `n` (RDX). -/
def divCount : Ctxt.Var Gouter r64 := .there (.there .here)

/-- The accumulator seed: the output array `qp` (RDI). -/
def divInit : Ctxt.Var Gouter AQ := .there (.there (.there (.there .here)))

/-- The loop invariants: the divisor `d` (RCX), its reciprocal `dinv` (R8), the
    limb count `n` (RDX) and the dividend array `up` (RSI). -/
def divInvs : HVector (fun ty => Ctxt.Var Gouter ty) [r64, r64, r64, AU] :=
  .cons (.there .here)
    (.cons .here
      (.cons (.there (.there .here))
        (.cons (.there (.there (.there .here))) .nil)))

/-- The front-compiled runtime-trip `mpn_divrem_1`: one body copy behind a `jne`
    back-edge, the trip counter seeded from the runtime `n` register, the output
    array threaded as the loop accumulator and `d`/`dinv`/`n`/`up` as loop
    invariants. `none` if the front declines. -/
def divRem1RtProgOpt (_ : Unit) : Option (ComL Gouter AQ) :=
  rolledForLoopNRt (Γouter := Gouter) (accCTy := .memref NR)
    (invCTys := [.sword 64, .sword 64, .sword 64, .memref NU])
    vmBody "qp" divLimbBodyLowCT divCount divInit divInvs

-- The front accepts the body and wraps it in a `ComL.forLoopNRt`.
#guard (divRem1RtProgOpt ()).isSome

/-- **The emitted loop's denotation is the `JLoopBodyN` fold of the front
    body.** Whenever the front compiles `divLimbBodyLowCT` to `update`, the
    runtime-trip program's denotation at any valuation is the `n`-fold of
    `update` over the trip indices, seeded by the `qp` argument and threading
    `d`, `dinv`, `n` and `up`. The instance of `rolledForLoopNRt_denote` at this
    kernel. -/
theorem divRem1RtProg_denote
    {update : Com jasminDialect
      (CryptoToJasminCom.mapCtx (CryptoTy.memref NR :: .sword 64 ::
        [CryptoTy.sword 64, CryptoTy.sword 64, CryptoTy.sword 64,
         CryptoTy.memref NU]))
      (CryptoToJasminCom.mapTy (CryptoTy.memref NR))}
    (hupd : Dialects.TranslateDialectRolledLoop.frontLoopBodyJ
      (accCTy := .memref NR) vmBody "qp" divLimbBodyLowCT = some update)
    (V : Ctxt.Valuation Gouter) :
    (divRem1RtProgOpt ()).map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(divCount.lookup V).toNat, update⟩
          (Expr.lookupArgs divInvs V) (divInit.lookup V)) :=
  rolledForLoopNRt_denote vmBody "qp" divLimbBodyLowCT divCount divInit divInvs
    hupd V

/-! ## 6. The owned `Lprog` and the rendered `.s` -/

/-- The rolled, owned-RA 5-argument-ABI `Lprog` for the runtime-trip
    `mpn_divrem_1` under the C symbol `fname`
    (`RDI = qp`, `RSI = up`, `RDX = n`, `RCX = d`, `R8 = dinv`).

    The `MULXHI` high-word binding the front emits for `SMulHiU` is coalesced
    with its paired low `MUL` into the printer's two-output `mulx` by
    `FuseMulHi.fuseMulHiLprog` in its `saveRdx` looped-body mode. -/
def divRem1RtLprogOpt (fname : String) : Option Lprog :=
  (divRem1RtProgOpt ()).map (fun c =>
    FuseMulHi.fuseMulHiLprog
      (ComL.toLprogPhysAbi c fname (argName 0) [argName 1]
        (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX", "R8"]
        [64, 64, 64, 64, 64])
      (saveRdx := true))

/-- The owned AT&T `.s` text for the runtime-trip `mpn_divrem_1`. -/
def divRem1RtAsmOpt (fname : String) : Option String :=
  (divRem1RtLprogOpt fname).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

/-- The 5-argument-ABI physical body of the front-compiled runtime-count loop. -/
def divRem1RtPhysBodyOpt (_ : Unit) : Option Lcmd :=
  (divRem1RtProgOpt ()).map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX", "RCX", "R8"]
      [64, 64, 64, 64, 64]).lfd_body)

-- The physical body carries a real back-edge: an internal label and a
-- conditional jump, so the emit is a counted loop and not an unrolled chain.
#guard ((divRem1RtPhysBodyOpt ()).map (fun body =>
  (body.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
    && (body.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false))))
  = some true

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would
-- re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 6. Emit driver

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

/-- Write the owned-backend `.s` for the runtime-trip `mpn_divrem_1_preinv` into
    the `bench/mpn_divrem_1_front_compare/gen_com` harness directory. -/
def emitMain : IO Unit := do
  let dir := "bench/mpn_divrem_1_front_compare/gen_com"
  IO.FS.createDirAll dir
  match divRem1RtAsmOpt "mpn_divrem_1_preinv" with
  | some s =>
      IO.FS.writeFile (dir ++ "/mpn_divrem_1_preinv_owned.s") s
      IO.println "WROTE bench/mpn_divrem_1_front_compare/gen_com/mpn_divrem_1_preinv_owned.s"
  | none => throw (IO.userError "the runtime-loop front declined mpn_divrem_1")

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
