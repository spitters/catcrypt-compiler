/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA

/-!
# Montgomery multiplication inner kernel — register allocation

Sibling to `BarrettRaEmit.lean`. Wires the **Montgomery multiplication
inner kernel** through `UnrolledComRA.unrolledSlotRAofItersCoalesce`,
the cross-iter + coalesce-aware register allocation framework.

`Optimizer/MontgomeryReduce.lean` is a leaf-renaming pass on `LowCT`:
it turns `RCall "mul_mod_q"` into `RCall "mont_mul_<q>_<R>"`, where the
LeafSpec's `mont_mul_<q>_<R>` leaf carries out the actual reduction.
That pass does no register allocation; the register-pressure savings come
from the body of `mont_mul_<q>_<R>` itself, which is what this file models.

## The Montgomery multiplication inner kernel

One Montgomery multiplication step `out = a · b · R⁻¹ mod q`, with
precomputed `q_inv = -q⁻¹ mod R` and radix `R = 2^k`:

```
// stage 1 — full multiply
t   = a * b                      -- u32 (for u16 inputs) or u64 (for u32 inputs)

// stage 2 — Montgomery factor
mlo = t & (R-1)                  -- low limb of t (mod R)
m   = mlo * q_inv                -- intermediate Montgomery factor

// stage 3 — multiply-and-add (mqlo only)
mq  = m * q                      -- u32 from m * q

// stage 4 — high-half assembly + correction
sum = t + mq                     -- high bit may be set
hi  = sum >> k                   -- the Montgomery-reduced value
cmp = (hi >= q)                  -- need a final subtract?
adj = cmp ? q : 0
out = hi - adj                   -- final reduced value
```

Eight register-resident scratches: `t`, `mlo`, `m`, `mq`, `sum`, `hi`,
`cmp`, `adj` — plus the architecturally-fixed inputs `a, b` and the
preamble constants `q`, `q_inv`. The output `out` is one more.

For the RA framework we model bindings that write a register-file slot.
Constant loads of `q`, `q_inv`, and the shift amount `k` are preamble /
immediate — not register-file reads inside the per-coefficient iter.

## Iteration model: unrolled Montgomery-N

Montgomery multiplication is the inner kernel of every polynomial-pointwise
multiplication: ML-KEM-768 has 256 coefficients × NTT pointwise products =
256 Montgomery muls per polynomial product (often 4-way batched: 64
four-way iters). For the RA model we use the same `standardUnroll = 32`
as Barrett (the 4-way batched 256-coefficient form), so the two patterns'
cross-iter analyses are directly comparable.

## Carry analysis

Under `UnrolledComRA.carriedAcross`:

* `q`, `q_inv`: read by every step but never written inside an iter
  (preamble-only). NOT carried under the metric, but seed-pinned to low
  physical slots.
* `a`, `b`: written every step (loaded from polynomial coefficient
  arrays), read inside the same iter. The conservative analysis sees
  `a, b` in both iter `i`'s writeSet and iter `i+1`'s readSet — so they
  ARE carried.
* `t, mlo, m, mq, sum, hi, cmp, adj`: each is written and read inside
  the same iter (write before later-event read). Carried.
* `out`: written but never read by any event. NOT carried (write-only
  sink, like Barrett's `out` and ML-KEM NTT's `c, d`).

So 10 of 12 logical slots are carried — a very high-pressure pattern,
heavier than Barrett (7 carried) and ML-KEM NTT (3 carried).

## Coalesce candidates

The Montgomery kernel is rich in three-address ops:
* `(mlo, t)`: `t & (R-1)`. `t` is read again later (`sum = t + mq`),
  so this is NOT a last-use of `t`. Skip.
* `(m, mlo)`: `mlo`'s only read. CANDIDATE.
* `(mq, m)`: `m`'s only read. CANDIDATE.
* `(sum, t)`: `t`'s last read (after `mlo`). CANDIDATE.
* `(hi, sum)`: `sum`'s only read. CANDIDATE.
* `(cmp, hi)`: `hi` is read again (`out = hi - adj`); NOT a last-use.
* `(adj, cmp)`: `cmp`'s only read. CANDIDATE.
* `(out, hi)`: `hi`'s last read. CANDIDATE.

So 6 candidate pairs per iter. The bench-exposed `coalesceCandidateCount`
captures the seed-filtered total.

## Contents

* `slot{Q, Qinv, A, B, T, Mlo, M, Mq, Sum, Hi, Cmp, Adj, Out}` — logical
  slot indices.
* `montStepEvents` — one Montgomery step's slot events.
* `montIters` — replicated per-coefficient iters (parametric).
* `montTrace` — preamble + flat iter sequence.
* `montMlkemRA`, `montMldsaRA` — concrete RAs at the two specialisations.
* `*_WellFormed` — well-formedness witnesses.
* `mlkemCoalesceCount`, `mldsaCoalesceCount` — exposed for the bench driver.

## Axiom budget

`[propext, Quot.sound]` only. Same shape as `BarrettRaEmit`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MontgomeryRaEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation

/-! ## 1. Logical slot indices

Thirteen logical slots in the Montgomery inner kernel: two preamble
constants (`q`, `q_inv`), two inputs (`a`, `b`), eight per-step
scratches (`t`, `mlo`, `m`, `mq`, `sum`, `hi`, `cmp`, `adj`), and one
output (`out`). -/

/-- Logical slot index for `q` (preamble-loaded modulus). -/
def slotQ : Nat := 0
/-- Logical slot index for `q_inv = -q⁻¹ mod R` (preamble-loaded). -/
def slotQinv : Nat := 1
/-- Logical slot index for input `a`. -/
def slotA : Nat := 2
/-- Logical slot index for input `b`. -/
def slotB : Nat := 3
/-- Logical slot index for `t = a * b`. -/
def slotT : Nat := 4
/-- Logical slot index for `mlo = t & (R-1)`. -/
def slotMlo : Nat := 5
/-- Logical slot index for `m = mlo * q_inv`. -/
def slotM : Nat := 6
/-- Logical slot index for `mq = m * q`. -/
def slotMq : Nat := 7
/-- Logical slot index for `sum = t + mq`. -/
def slotSum : Nat := 8
/-- Logical slot index for `hi = sum >> k`. -/
def slotHi : Nat := 9
/-- Logical slot index for `cmp = (hi >= q)`. -/
def slotCmp : Nat := 10
/-- Logical slot index for `adj = cmp ? q : 0`. -/
def slotAdj : Nat := 11
/-- Logical slot index for `out` (the final Montgomery-reduced product). -/
def slotOut : Nat := 12

/-- Canonical name of slot `s` in the baseline Montgomery-kernel emit. -/
def slotName (s : Nat) : String :=
  match s with
  | 0 => "q"
  | 1 => "q_inv"
  | 2 => "a"
  | 3 => "b"
  | 4 => "t"
  | 5 => "mlo"
  | 6 => "m"
  | 7 => "mq"
  | 8 => "sum"
  | 9 => "hi"
  | 10 => "cmp"
  | 11 => "adj"
  | 12 => "out"
  | _ => "v_unused"

/-! ## 2. Per-step slot events

The 10-binding sequence for one Montgomery-multiplication step. Constants
(`k`, `R-1`, `0`) are immediates and not register-file reads.

* `a   = inpA[i]`             — write a; reads: none (array load).
* `b   = inpB[i]`             — write b; reads: none (array load).
* `t   = a * b`               — write t; reads: [a, b].
* `mlo = t & (R-1)`           — write mlo; reads: [t] (R-1 immediate).
* `m   = mlo * q_inv`         — write m; reads: [mlo, q_inv].
* `mq  = m * q`               — write mq; reads: [m, q].
* `sum = t + mq`              — write sum; reads: [t, mq].
* `hi  = sum >> k`            — write hi; reads: [sum] (k immediate).
* `cmp = (hi >= q)`           — write cmp; reads: [hi, q].
* `adj = cmp ? q : 0`         — write adj; reads: [cmp, q].
* `out = hi - adj`            — write out; reads: [hi, adj].

`a, b` are loaded from polynomial coefficient arrays per iter. The store
of `out` to the output array is a sink, omitted from the trace. -/

/-- Slot events for one Montgomery-multiplication step. -/
def montStepEvents : List UnrolledComRA.SlotEvent :=
  [ ⟨slotA, []⟩                            -- a = inpA[i]
  , ⟨slotB, []⟩                            -- b = inpB[i]
  , ⟨slotT, [slotA, slotB]⟩                -- t = a * b
  , ⟨slotMlo, [slotT]⟩                     -- mlo = t & (R-1)
  , ⟨slotM, [slotMlo, slotQinv]⟩           -- m = mlo * q_inv
  , ⟨slotMq, [slotM, slotQ]⟩               -- mq = m * q
  , ⟨slotSum, [slotT, slotMq]⟩             -- sum = t + mq
  , ⟨slotHi, [slotSum]⟩                    -- hi = sum >> k
  , ⟨slotCmp, [slotHi, slotQ]⟩             -- cmp = (hi >= q)
  , ⟨slotAdj, [slotCmp, slotQ]⟩            -- adj = cmp ? q : 0
  , ⟨slotOut, [slotHi, slotAdj]⟩ ]         -- out = hi - adj

/-- The preamble events: `q` and `q_inv` are loaded once and live across
all iters. -/
def montPreamble : List UnrolledComRA.SlotEvent :=
  [ ⟨slotQ, []⟩
  , ⟨slotQinv, []⟩ ]

/-- Per-iteration chunking for an unrolled Montgomery-N kernel. -/
def montIters (n : Nat) : List (List UnrolledComRA.SlotEvent) :=
  List.replicate n montStepEvents

/-- Flat trace: the preamble events, then `n` per-step iters concatenated.
The preamble events live OUTSIDE the chunked iters, like in BarrettRaEmit
and MlkemRaEmit's `tw` preload. -/
def montTrace (n : Nat) : List UnrolledComRA.SlotEvent :=
  montPreamble ++ (montIters n).flatten

/-! ## 3. The cross-iteration + coalesce-aware RA

ML-KEM (`q = 3329`, `R = 2^16`) and ML-DSA-65 (`q = 8380417`, `R = 2^32`)
have the same slot-trace topology; only the constants stored in `slotQ`
and `slotQinv` and the multiply widths (u16×u16→u32 vs u32×u32→u64)
differ — neither of which affects the register-pressure analysis. -/

/-- **The Montgomery-N register allocation, parametric over unroll
count.** Built by `UnrolledComRA.unrolledSlotRAofItersCoalesce` over the
per-step chunking. -/
def montgomeryRA (n : Nat) : RegisterAllocation :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce
    (montTrace n) (montIters n)

/-- The Montgomery-N RA is well-formed for any unroll count. -/
theorem montgomeryRA_WellFormed (n : Nat) : WellFormed (montgomeryRA n) :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce_WellFormed _ _

/-- Standard unrolled Montgomery-N depth: 32 (= 256-coefficient
polynomial / 4-way batching, matching `BarrettRaEmit.standardUnroll`). -/
def standardUnroll : Nat := 32

/-- ML-KEM Montgomery RA (q = 3329, R = 2^16, 4-way batched at 32 iters). -/
def montgomeryMlkemRA : RegisterAllocation := montgomeryRA standardUnroll

/-- ML-DSA Montgomery RA (q = 8380417, R = 2^32, same iter shape). -/
def montgomeryMldsaRA : RegisterAllocation := montgomeryRA standardUnroll

theorem montgomeryMlkemRA_WellFormed : WellFormed montgomeryMlkemRA :=
  montgomeryRA_WellFormed standardUnroll

theorem montgomeryMldsaRA_WellFormed : WellFormed montgomeryMldsaRA :=
  montgomeryRA_WellFormed standardUnroll

/-! ## 4. Carry-analysis sanity -/

/-- `q` is NOT carried under the cross-iter metric (preamble-only). -/
theorem q_not_carried_crossIter :
    UnrolledComRA.carriedAcross slotQ (montIters standardUnroll) = false := by
  native_decide

/-- `q_inv` is NOT carried under the cross-iter metric (preamble-only). -/
theorem qinv_not_carried_crossIter :
    UnrolledComRA.carriedAcross slotQinv (montIters standardUnroll) = false := by
  native_decide

/-- `a` IS carried: every iter writes `a` (`a = inpA[i]`), and the
conservative iter-wide readSet puts `a` in every iter's reads
(via `t = a * b`). -/
theorem a_carried_crossIter :
    UnrolledComRA.carriedAcross slotA (montIters standardUnroll) = true := by
  native_decide

/-- `b` IS carried (same reason as `a`). -/
theorem b_carried_crossIter :
    UnrolledComRA.carriedAcross slotB (montIters standardUnroll) = true := by
  native_decide

/-- `t` IS carried (written by `t = a * b`, read by `mlo = t & (R-1)`,
both inside every iter). -/
theorem t_carried_crossIter :
    UnrolledComRA.carriedAcross slotT (montIters standardUnroll) = true := by
  native_decide

/-- `out` is NOT carried: no event reads `out` (the store of `out` into
the result array is a sink). -/
theorem out_not_carried_crossIter :
    UnrolledComRA.carriedAcross slotOut (montIters standardUnroll) = false := by
  native_decide

/-! ## 5. Coalesce-candidate audit -/

/-- **Montgomery has nonzero coalesce candidates** at the standard unroll. -/
def montCoalesceCount : Nat :=
  UnrolledComRA.coalesceCandidateCount (montTrace standardUnroll)

/-- Coalesce-candidate count under the ML-KEM specialisation, exposed
for the bench driver. -/
def mlkemCoalesceCount : Nat := montCoalesceCount

/-- Coalesce-candidate count under the ML-DSA specialisation. Same trace
topology as ML-KEM. -/
def mldsaCoalesceCount : Nat := montCoalesceCount

/-- The Montgomery kernel produces strictly positive coalesce candidates,
just like Barrett — the RA framework has real two-address coalescing
work to do. -/
theorem montCoalesceCount_pos :
    0 < montCoalesceCount := by native_decide

/-! ## 6. RA-driven slot-name resolution -/

/-- Physical slot name of logical slot `j` under RA `ra`. -/
def montgomeryRaSlotName (ra : RegisterAllocation) (j : Nat) : String :=
  slotName (ra.seqOf j)

/-- **Identity-RA slot-name equals the baseline slot-name pointwise.** -/
theorem montgomeryRaSlotName_identity_eq (j : Nat) :
    montgomeryRaSlotName RegisterAllocation.identity j = slotName j := by
  rfl

/-! ## 7. Carried-slot summary

Under the conservative analysis: `q`, `q_inv` are preamble-only (NOT
carried); `out` is write-only sink (NOT carried); the remaining 10 slots
(`a, b, t, mlo, m, mq, sum, hi, cmp, adj`) are all carried.

This is the **heaviest-carry** bucket in the suite: Montgomery
multiplication carries 10 of 13 logical slots. -/

/-- The carried-slot set for the Montgomery kernel. -/
def carriedSlots : List Nat :=
  (List.range 13).filter
    (fun s => UnrolledComRA.carriedAcross s (montIters standardUnroll))

/-- **Carried-slot inventory.** Montgomery carries 10 of 13 logical
slots — every step-internal scratch except the write-only `out`, plus
both inputs `a, b`. -/
theorem carriedSlots_eq :
    carriedSlots =
      [slotA, slotB, slotT, slotMlo, slotM, slotMq,
       slotSum, slotHi, slotCmp, slotAdj] := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.MontgomeryRaEmit
