/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.X86CostModel
import CatCrypt.Crypto.Optimizer.RandomizedScheduleSearch

/-!
# In-order (Cortex-A/M-class) schedule cost model — where SLOTHY actually pays

`X86CostModel.scheduleCostV2` is an **out-of-order** lower bound:
`max(critical-path, port-pressure)`. Both halves are *order-independent* — the
critical path is the dependency-DAG longest path and the port load is a multiset
sum — so **instruction scheduling cannot change it**. That is exactly why every
in-tree SLOTHY/CryptOpt experiment on a wide-OoO x86 core comes back null or
negative:

- `RandomizedScheduleSearch` §9 (#385), the Curve25519 field-mul `feMulBlock`:
  8 legal reschedules, all OoO-cost-neutral, within bench noise — never a win.
- `RandomizedScheduleSearch` §10 (#530), the three-product safegcd accumulate:
  the MULX-hoist the cost proxy prefers is **measured 20–30 % SLOWER** on a
  Ryzen 7 PRO 7840U (`bench/cryptopt_safegcd/cost_eval_3prod.c`).
- §1–8, the two-product pilot: 1.03× (`bench/cryptopt_safegcd`, null).

SLOTHY's literature targets are **in-order** cores (Cortex-M4/M55/M85,
Cortex-A55), where the hardware issues strictly in program order and *cannot*
hide a producer's latency behind later independent work unless the **static
schedule** already interleaves it. There static scheduling is the whole game.

This module adds the missing **in-order issue model** so the SLOTHY effect can
be measured in Lean without ARM silicon, and contrasts it with the OoO bound on
the *same* translation-validated blocks. The headline (Theorem
`hoist3_inOrder_lt__ooo_neutral`): the very 3-product reschedule that is
*measured slower* on OoO x86 is *strictly cheaper* under the in-order model —
the cross-microarchitecture crossover that explains the whole SLOTHY/CryptOpt
split.

**Placeholder notice** (inherited from `X86CostModel`): the per-instruction
latencies in `costOf` are coarse Skylake-class seeds, not Cortex-pipeline data.
The *structure* — single-issue in-order, operand-ready stalls, program-order
dependence — is the contribution; refresh the integers from the target core's
optimization guide before using as a production fitness function. The model is a
TCB-free steering heuristic: all soundness lives in the translation-validation
theorems of `RandomizedScheduleSearch`, which this module does not touch.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.InOrderCostModel

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc
open CatCrypt.Crypto.Optimizer.X86CostModel
open CatCrypt.Crypto.Optimizer.RandomizedScheduleSearch
  (inputBlock hoistedBlock input3Block hoist3Block feMulBlock
   writesFlags readsFlags)

/-! ## 1. Dependence footprints (registers + a carry-flag cell)

The in-order stall must serialise on the carry chain as well as on registers:
an `ADC` cannot issue until the flag-producing `ADD` ahead of it has retired.
We model the flag state as a single pseudo-register `"@cf"`; `writesFlags`/
`readsFlags` (from `RandomizedScheduleSearch`) decide membership. Registers use
the existing `writtenNames`/`readNames`. -/

/-- The carry-flag pseudo-register. -/
def cfCell : String := "@cf"

/-- All value-names an instruction reads (registers + the flag cell if it reads
    a carry-in). -/
def readDeps (i : JInstr 64) : List String :=
  readNames i ++ (if readsFlags i then [cfCell] else [])

/-- All value-names an instruction writes (registers + the flag cell if it sets
    flags). -/
def writeDeps (i : JInstr 64) : List String :=
  writtenNames i ++ (if writesFlags i then [cfCell] else [])

/-! ## 2. The in-order issue simulator

A strictly in-order single-issue pipeline. We carry:

- `issueSlot` : the earliest cycle the next instruction may *issue* (program
  order forbids issuing before the previous instruction has occupied its slot).
- `ready`     : an association list `value-name ↦ cycle the value is available`
  (a producer's result is ready `latency` cycles after it issues).
- `maxComplete` : the latest completion cycle seen (the block's finishing time).

For instruction `i`:
- `opReady`  = latest ready-time over all of `i`'s read deps (it must wait for
  every operand);
- `issue`    = `max(issueSlot, opReady)` — in-order: cannot issue before the
  pipeline slot frees *and* cannot issue before operands arrive (an in-order
  core **stalls** here; an OoO core would run a later ready instruction instead);
- `complete` = `issue + latency`;
- each written dep becomes ready at `complete`;
- `issueSlot` advances by `recipThroughput` (the issue port is occupied that
  long).

The crucial difference from `criticalPathCost`: here a producer→consumer pair
that sits **adjacent** forces the consumer to absorb the full producer latency,
because the in-order slot cannot advance past independent work that the static
schedule did not place between them. Reordering that interleaves independent
work therefore lowers `inOrderCost` — exactly the SLOTHY move. -/

/-- In-order pipeline state. -/
structure IOState where
  /-- Earliest cycle the next instruction may issue. -/
  issueSlot : Nat
  /-- `value-name ↦ cycle the value becomes available`, most-recent-first. -/
  ready : List (String × Nat)
  /-- Latest completion cycle seen so far. -/
  maxComplete : Nat
  deriving Repr

/-- Ready-cycle of a value-name (0 if it was never produced — a block input,
    live from entry). Most-recent write wins (`find?` hits the head-prepended
    latest definition first). -/
def readyOf (ready : List (String × Nat)) (r : String) : Nat :=
  match ready.find? (fun p => p.1 == r) with
  | some p => p.2
  | none   => 0

/-- One in-order issue step. -/
def ioStep (st : IOState) (i : JInstr 64) : IOState :=
  let c := costOf i
  let opReady := (readDeps i).foldl (fun a r => Nat.max a (readyOf st.ready r)) 0
  let issue := Nat.max st.issueSlot opReady
  let complete := issue + c.latency
  let ready' := (writeDeps i).foldl (fun acc w => (w, complete) :: acc) st.ready
  { issueSlot := issue + c.recipThroughput
    ready := ready'
    maxComplete := Nat.max st.maxComplete complete }

/-- **In-order schedule cost**: the finishing cycle of `block` on a strictly
    in-order single-issue pipeline with the `costOf` latency/throughput model.
    Unlike `scheduleCostV2`, this is **program-order dependent** — it is the
    fitness function under which instruction scheduling (SLOTHY) has something to
    optimise. -/
def inOrderCost (block : List (JInstr 64)) : Nat :=
  (block.foldl ioStep ⟨0, [], 0⟩).maxComplete

/-! ## 3. Two-product safegcd accumulate — SLOTHY wins in-order, null on OoO

`inputBlock` (strict interleave) vs `hoistedBlock` (both MULX front-loaded), the
§1–8 pilot. On OoO the two are identical (Theorem `ooo_2prod_neutral`, matching
the measured 1.03× null); in-order the hoist strictly wins (the second MULX's
4-cycle latency overlaps the first product's accumulate instead of stalling). -/

-- In-order: hoisted finishes earlier than the naive interleave.
#eval inOrderCost inputBlock     -- naive
#eval inOrderCost hoistedBlock   -- hoisted (lower)

/-- SLOTHY win **in-order**: front-loading the two independent MULXes strictly
    lowers the in-order finishing time — the second multiply's latency overlaps
    the first product's accumulate rather than stalling the pipeline. -/
theorem hoisted_inOrder_lt_input : inOrderCost hoistedBlock < inOrderCost inputBlock := by
  native_decide

/-- Null **out-of-order**: the same reschedule does not move the OoO bound at all
    (the critical-path DAG and port multiset are identical). This is the in-Lean
    shadow of the `bench/cryptopt_safegcd` 1.03× measurement. -/
theorem ooo_2prod_neutral : scheduleCostV2 hoistedBlock = scheduleCostV2 inputBlock := by
  native_decide

/-! ## 4. Three-product safegcd accumulate — the crossover (#530 measured slower
    on OoO, faster in-order)

This is the sharp one. `RandomizedScheduleSearch` §10 *measured* `hoist3Block`
at **1.21–1.30× slower** than `input3Block` on a Ryzen 7 PRO 7840U — the
register-pressure of six live mul-outputs costs more than the (already-hidden)
multiply latency saves on a wide-OoO core. Yet the OoO *bound* is neutral, and
under the **in-order** model the hoist is strictly *cheaper*: an in-order core
cannot hide the multiply latency dynamically, so the static front-load is the
only way to overlap it. The same code, three microarchitecture verdicts —
exactly why SLOTHY ships for Cortex and not for desktop x86. -/

#eval inOrderCost input3Block    -- naive (higher: each MULX stalls its accumulate)
#eval inOrderCost hoist3Block    -- hoisted (lower in-order)

/-- **The crossover (machine-checked).** The three-product MULX-hoist is
    strictly cheaper under the in-order model, *while* the OoO bound stays
    neutral — and the on-CPU OoO bench (`cost_eval_3prod.c`) measured it 20–30 %
    *slower*. One reschedule, opposite verdicts across microarchitectures: the
    precise in-Lean statement of why instruction scheduling is an in-order-core
    optimisation. -/
theorem hoist3_inOrder_lt__ooo_neutral :
    inOrderCost hoist3Block < inOrderCost input3Block ∧
    scheduleCostV2 hoist3Block = scheduleCostV2 input3Block := by
  constructor <;> native_decide

/-! ## 5. Curve25519 field-mul (`feMulBlock`, X25519) — bound by naming on BOTH
    microarchitectures

`feMulBlock` is one of the four headline SLOTHY targets and a fully
translation-validated real kernel. The §9 finding was that its residual is
**register allocation, not scheduling**: every product reuses the `hi`/`lo`
output names, serialising the schedule by name. The in-order model corroborates
this independently — without renaming there is no schedule that overlaps the
column multiplies, so the in-order cost is already at the name-serialised floor.
This is the honest negative for X25519: SLOTHY *scheduling* does not help here on
either microarchitecture; the lever is renaming (#386). -/

#eval inOrderCost feMulBlock
#eval scheduleCostV2 feMulBlock

/-! ## 6. Representative inner-loop blocks for the other three targets

The §3–§4 blocks are real, TV'd safegcd/X25519 kernels. For the remaining three
SLOTHY targets we capture the **dependency structure of the inner loop** — the
thing the scheduler actually sees — as representative blocks. These are NOT
emitted-kernel-faithful (no TV theorem attaches); they model the producer→
consumer latency chains so the in-order-vs-OoO contrast can be read off. Clearly
labelled as representative. -/

/-- **NTT Cooley–Tukey butterfly** (representative), the ML-KEM/ML-DSA inner
    loop: `t = ζ·a[j+len] (montgomery)`, `a[j+len] = a[j] − t`, `a[j] = a[j] + t`.
    Two butterflies on disjoint indices; the naive form runs them serially, each
    multiply immediately consumed. -/
def nttButterflyNaive : List (JInstr 64) :=
  [ .mulx "th0" "tl0" (.reg "zeta") (.reg "a4")   -- t0 = zeta * a[j+len]   (lane 0)
  , .sub  "a4" (.reg "tl0")                        -- a[j+len] = a[j] - t0   (stalls on t0)
  , .add  "a0" (.reg "tl0")                        -- a[j]     = a[j] + t0
  , .mulx "th1" "tl1" (.reg "zeta") (.reg "a5")   -- t1 = zeta * a[j+len+1] (lane 1)
  , .sub  "a5" (.reg "tl1")                        -- stalls on t1
  , .add  "a1" (.reg "tl1") ]

/-- Butterfly with both montgomery multiplies hoisted (representative SLOTHY
    move): the second multiply's latency overlaps the first butterfly's add/sub. -/
def nttButterflyHoisted : List (JInstr 64) :=
  [ .mulx "th0" "tl0" (.reg "zeta") (.reg "a4")
  , .mulx "th1" "tl1" (.reg "zeta") (.reg "a5")
  , .sub  "a4" (.reg "tl0")
  , .add  "a0" (.reg "tl0")
  , .sub  "a5" (.reg "tl1")
  , .add  "a1" (.reg "tl1") ]

#eval inOrderCost nttButterflyNaive
#eval inOrderCost nttButterflyHoisted

/-- NTT butterfly: hoisting the montgomery multiplies wins in-order (lane-disjoint
    multiplies overlap), neutral on OoO. The ML-KEM/ML-DSA inner-loop analogue of
    §3. -/
theorem ntt_inOrder_lt__ooo_neutral :
    inOrderCost nttButterflyHoisted < inOrderCost nttButterflyNaive ∧
    scheduleCostV2 nttButterflyHoisted = scheduleCostV2 nttButterflyNaive := by
  constructor <;> native_decide

/-- **Poly1305 multiply-accumulate** (representative): two 64×64 limb products
    folded into a 128-bit accumulator via the single-CF idiom, the MAC inner
    step. Same accumulate shape as the safegcd two-product, distinct operands. -/
def poly1305MacNaive : List (JInstr 64) :=
  [ .mulx "ph0" "pl0" (.reg "r0") (.reg "h0")
  , .add  "acc_lo" (.reg "pl0")
  , .adc  "acc_hi" (.reg "ph0")
  , .mulx "ph1" "pl1" (.reg "r1") (.reg "h1")
  , .add  "acc_lo" (.reg "pl1")
  , .adc  "acc_hi" (.reg "ph1") ]

/-- Poly1305 MAC with both products' multiplies hoisted. -/
def poly1305MacHoisted : List (JInstr 64) :=
  [ .mulx "ph0" "pl0" (.reg "r0") (.reg "h0")
  , .mulx "ph1" "pl1" (.reg "r1") (.reg "h1")
  , .add  "acc_lo" (.reg "pl0")
  , .adc  "acc_hi" (.reg "ph0")
  , .add  "acc_lo" (.reg "pl1")
  , .adc  "acc_hi" (.reg "ph1") ]

#eval inOrderCost poly1305MacNaive
#eval inOrderCost poly1305MacHoisted

/-- Poly1305 MAC: hoist wins in-order, neutral on OoO. -/
theorem poly1305_inOrder_lt__ooo_neutral :
    inOrderCost poly1305MacHoisted < inOrderCost poly1305MacNaive ∧
    scheduleCostV2 poly1305MacHoisted = scheduleCostV2 poly1305MacNaive := by
  constructor <;> native_decide

/-- **Keccak θ-step** (representative): the column-parity XOR/rotate-fold chain.
    Five column parities are independent; the naive form computes a parity and
    immediately folds it, the hoisted form batches the independent parities. XOR
    is 1-cycle so the in-order win here is smaller than for the multiply chains —
    a faithful datum: Keccak's SLOTHY headroom is in load/rotate scheduling and
    register pressure, less in latency hiding. -/
def keccakThetaNaive : List (JInstr 64) :=
  [ .xor_ "c0" (.reg "a0")    -- parity of column 0 (partial)
  , .xor_ "c0" (.reg "a5")
  , .xor_ "d1" (.reg "c0")    -- fold parity into lane (consumes c0)
  , .xor_ "c1" (.reg "a1")    -- parity of column 1
  , .xor_ "c1" (.reg "a6")
  , .xor_ "d2" (.reg "c1") ]

/-- Keccak θ with the two column parities computed before either fold. -/
def keccakThetaHoisted : List (JInstr 64) :=
  [ .xor_ "c0" (.reg "a0")
  , .xor_ "c0" (.reg "a5")
  , .xor_ "c1" (.reg "a1")
  , .xor_ "c1" (.reg "a6")
  , .xor_ "d1" (.reg "c0")
  , .xor_ "d2" (.reg "c1") ]

#eval inOrderCost keccakThetaNaive
#eval inOrderCost keccakThetaHoisted

/-- Keccak θ: the reschedule is OoO-neutral and in-order **no worse** (≤). With
    1-cycle XORs the in-order latency-hiding headroom is marginal — the honest
    finding that Keccak's scheduling lever is loads/rotates/regpressure, not the
    latency overlap that drives the multiply kernels. -/
theorem keccak_inOrder_le__ooo_neutral :
    inOrderCost keccakThetaHoisted ≤ inOrderCost keccakThetaNaive ∧
    scheduleCostV2 keccakThetaHoisted = scheduleCostV2 keccakThetaNaive := by
  constructor <;> native_decide

end CatCrypt.Crypto.Optimizer.InOrderCostModel
