/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Optimizer.SchedulerPass
public import CatCrypt.Crypto.Optimizer.SchedulerPass

/-!
# Validation of the ILP scheduler on the safegcd-62 Montgomery chain

This file applies `Optimizer.SchedulerPass.scheduleBlock` to a basic
block modelled on the **latency-bound accumulate chain** of the
safegcd-62 divstep modular inverse
(`CatCrypt/Crypto/Vale/SafegcdDivstep62Emit.lean`, READ-ONLY — we apply
the pass here, we do not edit the kernel).

The hot path that the bench README flags as the residual
cost is `accAddProd`: an open-coded i128 multiply-accumulate.  Each
`accAddProd acc a b` is a straight-line run of `RScalarSetExpr`s:

```
plo  := a *  b          (#IMUL low word)
phi  := a *h b          (#IMUL high word — long latency)
nlo  := acc_lo + plo
acc_lo := nlo
acc_hi := acc_hi + phi
```

Two consecutive products into **different accumulators** (the cd / ce
matrix passes accumulate four such products per limb) are
data-independent: the second product's two `#IMUL`s do not depend on the
first product's carry-add chain.  On a serial in-order schedule the
second `#IMUL` cannot issue until the first accumulator's `acc_hi`
add retires; an ILP scheduler hoists the independent multiplies up so
the second issues in the latency shadow of the first.

## What this file establishes

1. `scheduleBlock` **reorders** the block — `accBlockScheduled_order`
   pins the resulting write-var order (`native_decide`, since the
   fuelled schedule doesn't reduce in the kernel), showing the two
   `#IMUL` high-word multiplies (`phi1`, `phi2`) are pulled to the front;
   `accBlock_schedule_reorders` confirms the order changed.  The two
   main theorems below (`acc_schedule_denote_eq`,
   `acc_schedule_isCT_eq`) are NOT `decide`/`native_decide` — they are
   axiom-clean instances of the proven pass theorems.

2. The reorder is **denotationally identical** — `acc_schedule_denote_eq`
   is the instance of `scheduleBlock_denote_eq` for this block.  *This is
   the KAT byte-identity guarantee*: the scheduled kernel reaches exactly
   the same final state as the original from any start state, so its KAT
   output is byte-for-byte the original's (the schedule moved no data,
   only issue order).

3. The reorder **preserves constant-time** — `acc_schedule_isCT_eq` is
   the instance of `scheduleBlock_isCT_eq`: the all-public scalar block
   stays CT under any classification.

The companion C micro-bench (`bench/mpn_invert_safegcd_compare/
sched_microbench.c`) measures the two issue orders' cyc/op; see the
read-out in this module's closing docstring and the bench output.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SchedulerPassValidation

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Optimizer.SchedulerPass

/-! ## §1  The validation block (mirror of `accAddProd` ×2) -/

/-- A scalar read. -/
def v (x : String) : SExpr := .SVar x

/-- One `accAddProd`-shaped multiply-accumulate into `acc` of `a * b`,
    with product temps suffixed `t`.  Mirrors
    `SafegcdDivstep62Emit.accAddProd` reduced to its data-flow skeleton
    (the carry-bit-trick `_g{0,1,2}`/`cyy` ops are elided — they sit on
    the same serial `acc_lo`/`acc_hi` chain and don't change the
    independence structure between two products). -/
def prodChain (acc a b t : String) : List BBStmt :=
  [ .sset s!"plo{t}"   (.SMulS   (v a) (v b))                  -- #IMUL low word
  , .sset s!"phi{t}"   (.SMulHiS (v a) (v b))                  -- #IMUL high word (long-latency)
  , .sset s!"nlo{t}"   (.SAdd (v s!"{acc}_lo") (v s!"plo{t}")) -- 128-bit add, low
  , .sset s!"{acc}_lo" (v s!"nlo{t}")
  , .sset s!"{acc}_hi" (.SAdd (v s!"{acc}_hi") (v s!"phi{t}")) ]

/-- Two independent products, into accumulators `acc1` and `acc2`.  This
    is the multiply-accumulate shape of the cd / ce inner passes. -/
def accBlock : List BBStmt :=
  prodChain "acc1" "a1" "b1" "1" ++ prodChain "acc2" "a2" "b2" "2"

/-- The scheduled block. -/
def accBlockScheduled : List BBStmt := scheduleBlock accBlock

/-! ## §2  The scheduler reorders for ILP

The original issue order interleaves each product's `#IMUL`s with its own
serial carry chain.  After scheduling, both high-word `#IMUL`s (`phi1`,
`phi2` — the long-latency producers) are pulled to the front so the
second issues in the first's latency shadow, and both low `#IMUL`s
(`plo1`, `plo2`) cluster right after. -/

/-- The original write-var order (interleaved products). -/
theorem accBlock_order :
    accBlock.map BBStmt.writeVar
  = ["plo1", "phi1", "nlo1", "acc1_lo", "acc1_hi",
     "plo2", "phi2", "nlo2", "acc2_lo", "acc2_hi"] := by
  decide

/-- The scheduled write-var order: the two high-word `#IMUL`s lead, then
    the two low `#IMUL`s, then the (necessarily serial) carry chains.
    The independent long-latency producers now issue back-to-back. -/
theorem accBlockScheduled_order :
    accBlockScheduled.map BBStmt.writeVar
  = ["phi1", "phi2", "plo1", "plo2", "nlo1", "acc1_lo", "acc1_hi",
     "nlo2", "acc2_lo", "acc2_hi"] := by
  -- `scheduleBlock`'s fuelled recursion does not reduce in the kernel
  -- (`decide`); evaluating the concrete schedule needs the compiler.
  native_decide

/-- The schedule actually changed the program order — derived from the
    two explicit order computations (no further evaluation of
    `scheduleBlock`). -/
theorem accBlock_schedule_reorders :
    accBlockScheduled.map BBStmt.writeVar ≠ accBlock.map BBStmt.writeVar := by
  rw [accBlockScheduled_order, accBlock_order]; decide

/-! ## §3  Denotation preservation = KAT byte-identity

The scheduled block reaches the same final state as the original from any
start state.  Applying the same start state and reading the same output
slots therefore yields byte-identical results — this is the formal
content of "the schedule must not change the KAT". -/

/-- **KAT byte-identity (formal).**  For every fuel `N`, leaf spec, and
    start state, the scheduled `accBlock` and the original reach exactly
    the same final states.  Instance of `scheduleBlock_denote_eq`. -/
theorem acc_schedule_denote_eq (N : Nat) (leafSpec : LeafSpec)
    (rs rs' : RustState) :
    RustExec N leafSpec (blockToCmd accBlockScheduled) rs rs'
  ↔ RustExec N leafSpec (blockToCmd accBlock) rs rs' := by
  unfold accBlockScheduled
  exact scheduleBlock_denote_eq N leafSpec accBlock rs rs'

/-! ## §4  Constant-time preservation -/

/-- **CT preservation.**  The scheduled block has the same constant-time
    classification as the original under any level table / leaf-CT table.
    Instance of `scheduleBlock_isCT_eq`. -/
theorem acc_schedule_isCT_eq (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (blockToCmd accBlockScheduled) lt leafCT
  = cmdCT (blockToCmd accBlock) lt leafCT := by
  unfold accBlockScheduled
  exact scheduleBlock_isCT_eq lt leafCT accBlock

/-- The block is constant-time under the all-public classification (every
    slot is a public-modulus / public-iteration intermediate — the
    safegcd kernel is CT in the secret input `a`). -/
theorem accBlock_isCT :
    cmdCT (blockToCmd accBlock) LevelTable.allPublic LeafCTTable.canonical = true := by
  decide

/-- Hence the scheduled block is constant-time too. -/
theorem accBlockScheduled_isCT :
    cmdCT (blockToCmd accBlockScheduled) LevelTable.allPublic LeafCTTable.canonical = true := by
  rw [acc_schedule_isCT_eq]; exact accBlock_isCT

/-! ## §5  Honest read on the ILP win

The denotation theorem guarantees the schedule is **free** (no
correctness or CT cost).  Whether it *helps* is an empirical question
answered by the C micro-bench:

* The reorder clusters the two independent `#IMUL` high-word multiplies
  (`phi1`, `phi2`) at the front.  On an in-order or latency-exposed core
  this lets the second multiply issue in the first's 3–4-cycle shadow,
  shortening the critical path by roughly one multiply latency per pair.

* On a wide out-of-order core (Zen4 / Skylake), the CPU's own scheduler
  already reorders across this window — the reservation stations hold
  both products' multiplies regardless of static issue order.

**Measured result** (`bench/mpn_invert_safegcd_compare/sched_microbench.c`,
Ryzen 7 PRO 7840U / Zen4, MIN-of-REPS rdtsc): scheduled and unscheduled
issue orders tie at ~3 cyc/op (ratio 1.000), with KAT byte-identity
(0 mismatch / 100000).  This is a **negative result**: the static ILP schedule
is a free, verified transform but
yields no measurable speedup on this wide-OoO core, because the hardware
already reorders the two independent multiplies.  Static scheduling of
this shape pays on narrow-OoO / in-order targets, not Zen4-class CPUs. -/

end CatCrypt.Crypto.Optimizer.SchedulerPassValidation
