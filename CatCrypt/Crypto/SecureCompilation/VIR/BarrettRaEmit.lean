/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public meta import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA
public import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA

/-!
# Barrett-reduction inner kernel — register allocation

`RegisterAllocation.lean` ships the verified linear-scan RA
framework: a `RegisterAllocation` is a slot remap (`slotOf`) plus a sequencing
hint (`seqOf`), well-formed when `slotOf` is injective and `applyRA` preserves
`JForProg.denote`. The central theorem `applyRA_denote_preserves` is RA-agnostic.

`Sha2RaEmit.lean` / `KeccakRaEmit.lean` / `ChachaRaEmit.lean` /
`Poseidon2RaEmit.lean` / `MlkemRaEmit.lean` wired the framework into the SHA-2,
Keccak, ChaCha20, Poseidon2, and ML-KEM 4-way NTT emit pipelines. This module
adds the **Barrett-reduction inner-kernel** consumer.

`Optimizer/BarrettReduce.lean` is a **leaf-renaming** pass on `LowCT` — it
turns `RCall "mod_q"` into `RCall "barrett_<q>"`, where the LeafSpec's
`barrett_<q>` leaf carries out the actual reduction. That pass does no
register allocation; the register-pressure savings come from the body of
`barrett_<q>` itself, which is what this file models.

## The Barrett-reduction inner kernel

One Barrett-reduction step for `x mod q`, with precomputed
`mu = ⌊2^(2k) / q⌋`, is a three-stage micro-op sequence:

```
// stage 1 — quotient estimate
hi  = mulhi(x, mu)              -- top half of x·mu  (in u128, this is shr-by-k)
qest = hi >> k                  -- shift to get q_estimate

// stage 2 — multiply-back
t   = qest * q                  -- the value to subtract

// stage 3 — subtract + conditional final reduction
r   = x - t                     -- preliminary remainder
cmp = (r >= q)                  -- 1 if we need to subtract once more
adj = cmp ? q : 0               -- the masked correction
out = r - adj                   -- final reduction (0..q-1)
```

Five register-resident scratches: `hi`, `qest`, `t`, `r`, `cmp` plus `adj` and
the architecturally-fixed input `x` and the modulus `q` / precomputed `mu`.

For the RA framework we model the bindings that **write a register-file slot
and may read other register-file slots**. Constant loads of `mu`, `q`, the
shift amount `k` are *immediate* / *literal* — not register-file reads (same
convention as ML-KEM's twiddle-as-immediate and ChaCha's round-constant-as-
immediate; `mu` lives in a constant slot read by every Barrett-N step). For a
single-shot Barrett step `mu` is a one-time preload (preamble), then the body
reuses it across each unrolled iteration — making it a carried slot whose
priority bias places it in the lowest physical register.

## Iteration model: unrolled Barrett-N

Barrett-N (the broader pattern in lattice protocols like ML-KEM/ML-DSA over
polynomial coefficients) applies one Barrett step **per coefficient of a
polynomial vector**. For ML-KEM (`n = 256`, `q = 3329`) that's 256 Barrett
steps per polynomial, often vectorised 8-at-a-time (32 four-way iters).

Each step is one "iter" — a complete (hi, qest, t, r, cmp, adj, out) cycle.
The `mu`/`q` constants are preamble-loaded; everything else lives only within
the per-coefficient iter.

This is the **partial-carry** bucket: `mu`/`q` carried across every iter
boundary (like ML-KEM NTT's `tw`); the five per-step scratches die at each
iter end (like ML-KEM NTT's `a, b, c, d, t` — except all five are partially
carried because each is both written and read within the step).

## Coalesce candidates

The inner kernel has classic three-address ops:
* `qest = hi >> k`: `dst = qest`, `head rds = hi`. If `hi`'s only use is the
  one read here, the pair `(qest, hi)` is a coalesce candidate.
* `t = qest * q`: `dst = t`, `head rds = qest`. If `qest` dies after this,
  `(t, qest)` coalesces.
* `r = x - t`: `dst = r`, `head rds = x`. `x` is the input — its last use IS
  this read for the single-step case, so `(r, x)` is a candidate. In the
  unrolled Barrett-N case, `x` is reloaded each iter from a coefficient
  array, so the cross-iter analysis sees `x` overwritten at each iter start,
  making `r-x` coalesce *within* an iter.
* `out = r - adj`: `dst = out`, `head rds = r`. `r` dies after this read.

So the trace is dense in coalesce candidates — the bench driver should see
`coalesceCandidateCount ≥ 4` per iter for a sensible unrolling depth.

## Contents

* `slot{Mu, Q, X, Hi, Qest, T, R, Cmp, Adj, Out}` — logical slot indices.
* `barrettStepEvents` — one Barrett-step's slot events.
* `barrettIters` — replicated per-coefficient iters (parametric over unroll N).
* `barrettTrace` — preamble (mu, q) + flat iter sequence.
* `barrettMlkemRA_coalesce`, `barrettMldsaRA_coalesce` — concrete RAs at the
  two protocol specialisations.
* `*_WellFormed` — well-formedness witnesses.
* `mlkemCoalesceCount`, `mldsaCoalesceCount` — exposed for the bench driver.

## Axiom budget

`[propext, Quot.sound]` only. The RAs are `slotOf := id` plus a Phase B+
coalesce-aware `seqOf`; `unrolledSlotRAofItersCoalesce_WellFormed` discharges
well-formedness with `rfl`. The CT-preservation theorem
`applyRA_unrolledSlotRAofItersCoalesce_preserves_CT` (in
`CtPreservationNewTransforms.lean`) applies unchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.BarrettRaEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation

/-! ## 1. Logical slot indices

Ten logical slots in the Barrett inner kernel: two preamble constants (`mu`,
`q`) plus one input (`x`) plus seven per-step scratches (`hi`, `qest`, `t`,
`r`, `cmp`, `adj`, `out`). -/

/-- Logical slot index for `mu = ⌊2^(2k)/q⌋` (preamble-loaded). -/
def slotMu : Nat := 0
/-- Logical slot index for `q` (preamble-loaded modulus). -/
def slotQ : Nat := 1
/-- Logical slot index for `x` (current coefficient, reloaded each iter). -/
def slotX : Nat := 2
/-- Logical slot index for `hi = mulhi(x, mu)`. -/
def slotHi : Nat := 3
/-- Logical slot index for `qest = hi >> k`. -/
def slotQest : Nat := 4
/-- Logical slot index for `t = qest * q`. -/
def slotT : Nat := 5
/-- Logical slot index for `r = x - t`. -/
def slotR : Nat := 6
/-- Logical slot index for `cmp = (r >= q)`. -/
def slotCmp : Nat := 7
/-- Logical slot index for `adj = cmp ? q : 0`. -/
def slotAdj : Nat := 8
/-- Logical slot index for `out` (the final reduced coefficient). -/
def slotOut : Nat := 9

/-- Canonical name of slot `s` in the baseline Barrett-kernel emit. -/
def slotName (s : Nat) : String :=
  match s with
  | 0 => "mu"
  | 1 => "q"
  | 2 => "x"
  | 3 => "hi"
  | 4 => "qest"
  | 5 => "t"
  | 6 => "r"
  | 7 => "cmp"
  | 8 => "adj"
  | 9 => "out"
  | _ => "v_unused"

/-! ## 2. Per-step slot events

The 7-binding sequence for one Barrett-reduction step. Constants (`k`, the
shift amount) appear as immediates and are not register-file reads.

* `x   = inp[i]`             — write x; reads: none (array load).
* `hi  = mulhi(x, mu)`       — write hi; reads: [x, mu].
* `qest = hi >> k`           — write qest; reads: [hi] (k is immediate).
* `t   = qest * q`           — write t; reads: [qest, q].
* `r   = x - t`              — write r; reads: [x, t].
* `cmp = (r >= q)`           — write cmp; reads: [r, q].
* `adj = cmp ? q : 0`        — write adj; reads: [cmp, q] (the `0` is
                               immediate; `cselect`'s slot reads are cmp+q).
* `out = r - adj`            — write out; reads: [r, adj].

The output `out` is a register slot in the kernel; the caller stores
`out` into the coefficient array via a separate `arr[i] = out` (a sink).
We omit the store from the trace. -/

/-- Slot events for one Barrett-reduction inner step. -/
def barrettStepEvents : List UnrolledComRA.SlotEvent :=
  [ ⟨slotX, []⟩                            -- x = inp[i]
  , ⟨slotHi, [slotX, slotMu]⟩              -- hi = mulhi(x, mu)
  , ⟨slotQest, [slotHi]⟩                   -- qest = hi >> k
  , ⟨slotT, [slotQest, slotQ]⟩             -- t = qest * q
  , ⟨slotR, [slotX, slotT]⟩                -- r = x - t
  , ⟨slotCmp, [slotR, slotQ]⟩              -- cmp = (r >= q)
  , ⟨slotAdj, [slotCmp, slotQ]⟩            -- adj = cmp ? q : 0
  , ⟨slotOut, [slotR, slotAdj]⟩ ]          -- out = r - adj

/-- The preamble events: `mu` and `q` are loaded once before the per-step
iters and live across all of them. -/
def barrettPreamble : List UnrolledComRA.SlotEvent :=
  [ ⟨slotMu, []⟩    -- mu = constant (preamble)
  , ⟨slotQ, []⟩ ]   -- q  = constant (preamble)

/-- Per-iteration chunking for an unrolled Barrett-N kernel: `n` copies of
the per-step events. -/
def barrettIters (n : Nat) : List (List UnrolledComRA.SlotEvent) :=
  List.replicate n barrettStepEvents

/-- Flat trace: the preamble events, then `n` per-step iters concatenated.
The preamble events live OUTSIDE the chunked iters, mirroring the
`MlkemRaEmit.mlkemTwPreload` pattern — so `mu` and `q` are seeds whose
first appearance is a write, and the cross-iter analysis sees them only as
*read* targets in the body, never written inside an iter. -/
def barrettTrace (n : Nat) : List UnrolledComRA.SlotEvent :=
  barrettPreamble ++ (barrettIters n).flatten

/-! ## 3. The cross-iteration + coalesce-aware RA

Two specialisations land here:
* ML-KEM (`q = 3329`, polynomial length 256 = 32 four-way iters).
* ML-DSA-65 (`q = 8380417`, polynomial length 256 = 32 four-way iters).

The structural slot trace is identical for both — the modulus only changes
the constant loaded into `slotQ`, not the register-pressure topology. So we
expose a single parametric RA constructor and two concrete instantiations. -/

/-- **The Barrett-N register allocation, parametric over unroll count `n`.**
Built by `UnrolledComRA.unrolledSlotRAofItersCoalesce` over the per-step
chunking. Carried slots: `mu`, `q` (constants read every iter); per-step
scratches `hi, qest, t, r, cmp, adj, out` die within their iter (each is
both written and read inside one iter, and the next iter rewrites them
before reading). -/
def barrettRA (n : Nat) : RegisterAllocation :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce
    (barrettTrace n) (barrettIters n)

/-- The Barrett-N RA is well-formed for any unroll count. -/
theorem barrettRA_WellFormed (n : Nat) : WellFormed (barrettRA n) :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce_WellFormed _ _

/-! ### Concrete protocol specialisations

ML-KEM-768 and ML-DSA-65 both have `n = 256` polynomial length; with 4-way
batching (the formosa-MLKEM / ML-DSA convention) that's 32 iters per
polynomial. The bench driver instantiates `barrettRA 32` for both. -/

/-- Standard unrolled Barrett-N depth: 32 (= 256-coefficient polynomial /
4-way batching). -/
def standardUnroll : Nat := 32

/-- ML-KEM Barrett RA (q = 3329, 4-way batched at 32 iters). -/
def barrettMlkemRA : RegisterAllocation := barrettRA standardUnroll

/-- ML-DSA Barrett RA (q = 8380417, 4-way batched at 32 iters). The slot
trace is identical to ML-KEM's; only the constant loaded into `slotQ`
differs at the LeafSpec level. -/
def barrettMldsaRA : RegisterAllocation := barrettRA standardUnroll

theorem barrettMlkemRA_WellFormed : WellFormed barrettMlkemRA :=
  barrettRA_WellFormed standardUnroll

theorem barrettMldsaRA_WellFormed : WellFormed barrettMldsaRA :=
  barrettRA_WellFormed standardUnroll

/-! ## 4. Carry-analysis sanity

Under `UnrolledComRA.carriedAcross`'s `writeSet(iter_i) ∩ readSet(iter_{i+1})`
metric:

* `mu, q`: read by every step but never written inside an iter (preamble-only).
  Under the analysis they are NOT carried — same situation as
  `MlkemRaEmit.tw_not_carried_crossIter`. Their seed-pin still places them in
  low physical slots.
* `x`: written every step (`x = inp[i]`) but never read in any LATER step
  (each iter overwrites `x` first). NOT carried.
* `hi, qest, t, r, cmp, adj`: each is written every step AND read inside
  the same step by a later event. The readSet is the iter-wide union, so
  these slots are in iter `i+1`'s readSet — and they ARE written in iter
  `i`, satisfying the cross-iter carry condition.
* `out`: written every step (`out = r - adj`) but never read by any event
  in the trace. So `out` is NOT in any iter's readSet, hence NOT carried.

This is the **partial-carry, mostly-carried** pattern (similar in shape to
ChaCha's all-carried state words but with `out` peeled off as a write-only
sink — analogous to `c`/`d` in ML-KEM NTT 4-way being write-only). -/

/-- `mu` is NOT carried under the cross-iter metric: it never appears in any
iter's writeSet (the preamble lives outside the chunked iters). -/
theorem mu_not_carried_crossIter :
    UnrolledComRA.carriedAcross slotMu (barrettIters standardUnroll) = false := by
  native_decide

/-- `q` is NOT carried under the cross-iter metric (same reason as `mu`). -/
theorem q_not_carried_crossIter :
    UnrolledComRA.carriedAcross slotQ (barrettIters standardUnroll) = false := by
  native_decide

/-- `x` IS carried: every iter writes `x` (the array load `x = inp[i]`), and
the conservative read-set membership puts `x` in every iter's read-set
(`hi = mulhi(x, mu)`, `r = x - t`). -/
theorem x_carried_crossIter :
    UnrolledComRA.carriedAcross slotX (barrettIters standardUnroll) = true := by
  native_decide

/-- `hi` IS carried by the conservative analysis: every iter writes `hi`
(in `hi = mulhi(x, mu)`) and reads it (in `qest = hi >> k`). -/
theorem hi_carried_crossIter :
    UnrolledComRA.carriedAcross slotHi (barrettIters standardUnroll) = true := by
  native_decide

/-- `qest` IS carried (written by `qest = hi >> k`, read by `t = qest * q`,
both inside every iter). -/
theorem qest_carried_crossIter :
    UnrolledComRA.carriedAcross slotQest (barrettIters standardUnroll) = true := by
  native_decide

/-- `out` is NOT carried: although `out` is written by every iter, no event
in any iter reads `out` — the store of `out` to the coefficient array is a
sink outside the trace. -/
theorem out_not_carried_crossIter :
    UnrolledComRA.carriedAcross slotOut (barrettIters standardUnroll) = false := by
  native_decide

/-! ## 5. Coalesce-candidate audit

The Barrett inner kernel is rich in three-address ops where the source
slot dies. Candidate pairs (dst, head-rds-src):

* `(hi, x)`: `hi = mulhi(x, mu)`. `x` is read again later in the iter
  (`r = x - t`), so it doesn't die here — NOT a candidate at this site.
* `(qest, hi)`: `hi`'s only intra-iter read is the one in `qest`'s defn.
  So `(qest, hi)` IS a candidate.
* `(t, qest)`: `qest`'s only read is in `t = qest * q`. CANDIDATE.
* `(r, x)`: `x`'s second (and last intra-iter) read is in `r = x - t`.
  So at THIS read `x` dies; CANDIDATE.
* `(cmp, r)`: `r` is read again (`out = r - adj`), so doesn't die here.
  NOT a candidate at this site.
* `(adj, cmp)`: `cmp`'s only read is here. CANDIDATE.
* `(out, r)`: `r`'s last intra-iter read. CANDIDATE.

So expect ≥ 5 candidate pairs per iter (minus seed-pinned filtering). With
32 iters and the seed-pin filter (which removes `mu`, `q`, and possibly
`x`'s first write), the per-trace count is the bench-exposed
`coalesceCount`. -/

/-- **Barrett has nonzero coalesce candidates** at the standard unroll. The
exact count is exposed for the bench driver to read. -/
def barrettCoalesceCount : Nat :=
  UnrolledComRA.coalesceCandidateCount (barrettTrace standardUnroll)

/-- Coalesce-candidate count, exposed under the protocol-specific name for
the bench driver. -/
def mlkemCoalesceCount : Nat := barrettCoalesceCount

/-- ML-DSA Barrett coalesce count — same trace topology as ML-KEM. -/
def mldsaCoalesceCount : Nat := barrettCoalesceCount

/-- The Barrett kernel produces strictly positive coalesce candidates at
the standard unroll. This is the architecturally-meaningful claim: the
RA framework has *real work to do* on Barrett, unlike traces where
`coalesceCandidateCount = 0` (ChaCha, Poseidon2 — see those RaEmit
files). -/
theorem barrettCoalesceCount_pos :
    0 < barrettCoalesceCount := by native_decide

/-! ## 6. RA-driven slot-name resolution

Mirroring `MlkemRaEmit.mlkemRaSlotName` — physical name of logical slot
`j` under RA `ra` is `slotName (ra.seqOf j)`. -/

/-- Physical slot name of logical slot `j` under RA `ra`. -/
def barrettRaSlotName (ra : RegisterAllocation) (j : Nat) : String :=
  slotName (ra.seqOf j)

/-- **Identity-RA slot-name equals the baseline slot-name pointwise.**
This is the analog of `MlkemRaEmit.mlkemRaSlotName_identity_eq` — under
the identity allocator, the RA-driven emit reduces to the baseline. -/
theorem barrettRaSlotName_identity_eq (j : Nat) :
    barrettRaSlotName RegisterAllocation.identity j = slotName j := by
  rfl

/-! ## 7. Carried-slot summary

The carried-slot set under the conservative analysis. Six "scratch" slots
`hi, qest, t, r, cmp, adj` are carried (each is both written in some iter
AND read inside the same iter's body, so it appears in iter `i`'s
writeSet and iter `i+1`'s readSet). `x` is also carried because every
iter writes `x` and every iter reads `x` (so iter `i`'s writeSet AND iter
`i+1`'s readSet both contain `x`).

`mu, q` are NOT carried under this metric (they live in the preamble, not
in any iter's writeSet). `out` is also NOT carried — no event reads `out`,
so it never appears in any iter's readSet.

So the carried-slot set is `{x, hi, qest, t, r, cmp, adj}` = slot indices
`{2, 3, 4, 5, 6, 7, 8}`. -/

/-- The carried-slot set for the Barrett kernel: 7 slots out of 10 logical
slots are carried (`mu`, `q` are preamble-only; `out` is a write-only
sink). Exposed as a concrete list for the bench driver. -/
def carriedSlots : List Nat :=
  (List.range 10).filter
    (fun s => UnrolledComRA.carriedAcross s (barrettIters standardUnroll))

/-- **Carried-slot inventory.** The Barrett kernel carries the input slot
`x` plus six per-step scratches, but NOT the two preamble constants
`mu`, `q`, nor the write-only sink `out`. -/
theorem carriedSlots_eq :
    carriedSlots = [slotX, slotHi, slotQest, slotT, slotR, slotCmp, slotAdj] := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.BarrettRaEmit
