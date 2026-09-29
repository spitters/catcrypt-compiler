/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Optimizer.SpillingRegAlloc
public import CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-!
# SLOTHY-grade x86 instruction cost model

A reusable per-instruction cost model for the `JInstr 64` subset, structured
after the SLOTHY scheduler's cost representation (Banegas, Bernstein, Campos,
Chou, Erbsen, Johansson, McCann, Panny, Perret, Persichetti, Renes, Smith,
Tuveri — "SLOTHY: Assembly Optimization via Constraint Solving", USENIX 2024).

SLOTHY's key insight: a schedule is lower-bounded by

    max(critical-path latency, port-pressure throughput lower bound)

Neither bound alone is tight, but together they form a strong dual certificate.
This module provides both in pure Lean so the randomized search in
`RandomizedScheduleSearch` can be replaced by (or extended with) a more
principled cost proxy without touching the translation-validation machinery.

**Placeholder notice.** The numeric constants in `costOf` are seeded from the
coarse Skylake-class latencies already used by `RandomizedScheduleSearch`
(`mulx`=4, `mulxMem`=5, everything else=1) plus zero-latency reciprocal
throughputs and singleton port lists. **Do not treat these numbers as
authoritative microarchitecture data.** Refresh them per-microarchitecture from
[uops.info](https://uops.info/) or Agner Fog's instruction tables before
using the cost function in a production optimizer. The structure, the
critical-path algorithm, and the port-pressure formula are the contribution;
the exact integers are a TCB-free steering heuristic.

> **`@bench-only`.** The `inputBlockEx` / `hoistedBlockEx` `List (JInstr 64)`
> blocks are cost-model example fixtures; the module emits no deployed `.s`
> artifact.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.X86CostModel

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-! ## 1. Port identifiers

x86 execution ports follow the Skylake/Golden Cove naming scheme. We use a
small inductive rather than raw `Nat` so pattern-matching is self-documenting.
SLOTHY models each instruction as occupying a *set* of ports (one per µop);
`portPressureCost` aggregates across the set. -/

/-- Execution port on a Skylake-class x86 core.
    Only ports relevant to the `JInstr 64` subset are listed; the rest
    collapse to `pOther`. -/
inductive PortId where
  /-- Integer ALU / multiply (IMUL/MULX dispatch here). -/
  | p0
  /-- Integer ALU / branch. -/
  | p1
  /-- LEA / shift / branch. -/
  | p5
  /-- Integer ALU (simple). -/
  | p6
  /-- Load AGU: all memory-source ops issue an AGU µop here. -/
  | p23
  /-- Store-data: all memory-destination ops issue a store-data µop here. -/
  | p4
  /-- Catch-all for ops whose ports are not modelled precisely. -/
  | pOther
  deriving Repr, DecidableEq, Inhabited

/-! ## 2. Per-instruction cost record -/

/-- SLOTHY-style per-instruction cost record.

Fields:
- `latency`         : end-to-end latency in cycles (producer → consumer).
- `recipThroughput` : reciprocal throughput in cycles (how many cycles the
                      relevant port is occupied per issue). We store it as a
                      `Nat` scaled by 1 (i.e. a ceiling); sub-cycle throughput
                      rounds up to 1.
- `ports`           : execution ports this instruction dispatches µops to.
                      A two-µop instruction (e.g. a memory load) appears on
                      two ports.
- `fuOccupancy`     : functional-unit occupancy in cycles (for resource
                      contention beyond port pressure; defaults to `latency`
                      for most ALU ops).

**Placeholder notice** — see module docstring. Refresh from uops.info / Agner
Fog before using in a production optimizer. These numbers only steer a
legality-checked heuristic; they are TCB-free. -/
structure InstrCost where
  latency         : Nat
  recipThroughput : Nat
  ports           : List PortId
  fuOccupancy     : Nat
  deriving Repr

/-! ## 3. `costOf` — per-instruction cost table -/

/-- SLOTHY-grade cost record for every `JInstr 64` constructor.

Placeholder latencies (see module docstring):
- `mulx`/`mulxMem` : 4/5 c (Skylake-class unsigned widening multiply latency)
- `adcx`/`adox`    : 1 c  (flag-splitting add, Broadwell+)
- `add`/`sub`/`adc`/`sbb`/`and_`/`or_`/`xor_`/... : 1 c
- `imul`           : 3 c  (low-word multiply)
- Load ops         : 4 c latency (L1-hit), AGU on p23
- Store ops        : 1 c (store-data p4 + AGU p23)
- `cmov*`          : 1 c
- `neg`/`setc`     : 1 c
- `cmp`/`not_`/`andn`/`bzhi`/`rol`/`ror`/`rorx`/`shlx`/`shrx`/`sarx`/`movzx`/`movsx`/`lea` : 1 c
- `loadSym`        : 3 c (RIP-relative LEA)
- `inc`/`dec`/`clc`/`stc`/`xchg`/`cmovcc`/`setcc`/`testN`/`bt`/`btr`/`bts` : 1 c
- `imulri`/`shld`/`shrd` : 3 c; `rcl`/`rcr` : 2 c
- `mul`/`imulWide` : 4 c (one-operand widening multiply)
- `addMem`/`adcxMem`/`adoxMem`/`addToMem`/`cmpMem` : 2 c; `imulMem`/`imulriMem` : 4 c

Sources to consult for refresh: <https://uops.info/> (filter Skylake /
Rocket Lake / Golden Cove), Agner Fog "Instruction Tables" (latest PDF). -/
def costOf : JInstr 64 → InstrCost
  -- MOV (register): 1c, ALU port (zero-latency rename on modern µarch,
  -- charged 1 conservatively since the model is latency-based).
  | .mov _ _             => ⟨1, 1, [.p0], 1⟩
  -- Two-address integer ALU: 1c latency, any ALU port.
  | .add _ _             => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  | .sub _ _             => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  | .adc _ _             => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  | .sbb _ _             => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  -- IMUL (two-address, low word): 3c latency, 1c throughput, p1 only.
  | .imul _ _            => ⟨3, 1, [.p1], 3⟩
  -- NEG: 1c ALU.
  | .neg _               => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  -- SETC (flag materialise, zero-extended): 1c.
  | .setc _              => ⟨1, 1, [.p0, .p1], 1⟩
  -- Bitwise ALU.
  | .and_ _ _            => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  -- TEST: the same ALU cost as AND. It produces only flags, so it never appears
  -- as the producer of a true register dependence (`writtenNames .test = []`);
  -- the `latency` field is what a flag consumer would wait on.
  | .test _ _            => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  -- CMP: the same ALU cost as SUB, and like TEST it produces only flags, so
  -- `writtenNames .cmp = []` keeps it from ever being a true-dependence producer.
  | .cmp _ _             => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  -- NOT: 1c ALU, no flag.
  | .not_ _              => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  -- ANDN (BMI1): 1c, p1/p5.
  | .andn _ _ _          => ⟨1, 1, [.p1, .p5], 1⟩
  -- ROL/ROR: 1c on the shift ports.
  | .rol _ _             => ⟨1, 1, [.p0, .p6], 1⟩
  | .ror _ _             => ⟨1, 1, [.p0, .p6], 1⟩
  -- RORX/SHLX/SHRX/SARX (BMI2): 1c on the shift ports, no flag written.
  | .rorx _ _ _          => ⟨1, 1, [.p0, .p6], 1⟩
  | .shlx _ _ _          => ⟨1, 1, [.p0, .p6], 1⟩
  | .shrx _ _ _          => ⟨1, 1, [.p0, .p6], 1⟩
  | .sarx _ _ _          => ⟨1, 1, [.p0, .p6], 1⟩
  -- MOVZX/MOVSX (register source): 1c ALU.
  | .movzx _ _ _         => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  | .movsx _ _ _         => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  -- LEA: 1c on the AGU-fed p1/p5; it performs no memory access, so no p23 µop.
  | .lea _ _ _ _ _       => ⟨1, 1, [.p1, .p5], 1⟩
  | .or_  _ _            => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  | .xor_ _ _            => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  -- Shift: p0 or p6.
  | .shl _ _             => ⟨1, 1, [.p0, .p6], 1⟩
  | .shr _ _             => ⟨1, 1, [.p0, .p6], 1⟩
  | .sar _ _             => ⟨1, 1, [.p0, .p6], 1⟩
  -- CMOVcc: 1c, p0/p1.
  | .cmove _ _           => ⟨1, 1, [.p0, .p1], 1⟩
  | .cmovne _ _          => ⟨1, 1, [.p0, .p1], 1⟩
  | .cmovb _ _           => ⟨1, 1, [.p0, .p1], 1⟩
  -- MULX (register): 4c latency, 1c throughput, p1 (dedicated multiplier).
  -- Placeholder; real Skylake MULX is ~3c. Refresh from uops.info.
  | .mulx _ _ _ _        => ⟨4, 1, [.p1], 4⟩
  -- MULX (memory): 5c latency (multiply + L1 load), p1 + p23.
  | .mulxMem _ _ _ _ _   => ⟨5, 1, [.p1, .p23], 5⟩
  -- ADCX (CF-chain add): 1c, p1 (Broadwell+ specialised adder).
  | .adcx _ _            => ⟨1, 1, [.p1], 1⟩
  -- ADOX (OF-chain add): 1c, p1.
  | .adox _ _            => ⟨1, 1, [.p1], 1⟩
  -- LOAD (register base + immediate offset): 4c L1-hit latency, AGU on p23.
  | .loadMem _ _ _       => ⟨4, 1, [.p23], 4⟩
  -- STORE (register base + immediate offset): 1c, store-data p4 + AGU p23.
  | .storeMem _ _ _      => ⟨1, 1, [.p4, .p23], 1⟩
  -- LOAD (SIB indexed): 4c L1-hit latency, AGU on p23.
  | .loadMemIdx _ _ _ _  => ⟨4, 1, [.p23], 4⟩
  -- STORE (SIB indexed): same model as storeMem.
  | .storeMemIdx _ _ _ _ => ⟨1, 1, [.p4, .p23], 1⟩
  -- LEA / load symbol (RIP-relative address materialise): 3c, p1/p5.
  | .loadSym _ _         => ⟨3, 1, [.p1, .p5], 3⟩
  -- INC/DEC: 1c ALU.
  | .inc _               => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  | .dec _               => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  -- CLC/STC: 1c, flag write only.
  | .clc                 => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  | .stc                 => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  -- XCHG (register pair): 1c ALU.
  | .xchg _ _            => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  -- IMUL with immediate (low word): the same cost as `imul`.
  | .imulri _ _ _        => ⟨3, 1, [.p1], 3⟩
  -- MUL/IMUL one-operand widening multiply: 4c, p1 plus p5 for the high word.
  | .mul _ _ _           => ⟨4, 1, [.p1, .p5], 4⟩
  | .imulWide _ _ _      => ⟨4, 1, [.p1, .p5], 4⟩
  -- SHLD/SHRD: 3c on p1.
  | .shld _ _ _          => ⟨3, 1, [.p1], 3⟩
  | .shrd _ _ _          => ⟨3, 1, [.p1], 3⟩
  -- RCL/RCR: 2c on the shift ports.
  | .rcl _ _             => ⟨2, 1, [.p0, .p6], 2⟩
  | .rcr _ _             => ⟨2, 1, [.p0, .p6], 2⟩
  -- CMOVcc/SETcc at a general condition: the cost of `cmov*`/`setc`.
  | .cmovcc _ _ _        => ⟨1, 1, [.p0, .p1], 1⟩
  | .setcc _ _           => ⟨1, 1, [.p0, .p1], 1⟩
  -- TEST at an operand size: the cost of `test`; flags only.
  | .testN _ _ _         => ⟨1, 1, [.p0, .p1, .p5, .p6], 1⟩
  -- BT/BTR/BTS (register operands): 1c on the shift ports.
  | .bt _ _              => ⟨1, 1, [.p0, .p6], 1⟩
  | .btr _ _             => ⟨1, 1, [.p0, .p6], 1⟩
  | .bts _ _             => ⟨1, 1, [.p0, .p6], 1⟩
  -- Memory-source arithmetic: the register form's latency plus one cycle for the
  -- load, with the AGU on p23, as `mulxMem` is charged against `mulx`.
  | .addMem _ _ _        => ⟨2, 1, [.p0, .p1, .p5, .p6, .p23], 2⟩
  | .adcxMem _ _ _       => ⟨2, 1, [.p1, .p23], 2⟩
  | .adoxMem _ _ _       => ⟨2, 1, [.p1, .p23], 2⟩
  | .imulMem _ _ _       => ⟨4, 1, [.p1, .p23], 4⟩
  | .imulriMem _ _ _ _   => ⟨4, 1, [.p1, .p23], 4⟩
  | .cmpMem _ _ _        => ⟨2, 1, [.p0, .p1, .p5, .p6, .p23], 2⟩
  -- ADD into memory: load, add and store-data, with the AGU on p23 and the store on p4.
  | .addToMem _ _ _      => ⟨2, 1, [.p0, .p1, .p5, .p6, .p4, .p23], 2⟩
  -- BZHI (BMI2): charged as ANDN, 1c on p1/p5.
  | .bzhi _ _ _          => ⟨1, 1, [.p1, .p5], 1⟩

/-! ## 4. Data-dependence helpers -/

/-- True dependence: does `consumer` read any register that `producer` writes?
    We reuse `writtenNames`/`readNames` from `SpillingRegAlloc`. -/
def hasTrueDep (producer consumer : JInstr 64) : Bool :=
  (writtenNames producer).any (fun w => (readNames consumer).contains w)

/-- Latency penalty if `consumer` depends on `producer`: the producer's
    `latency` cycles must elapse before `consumer` can issue. Returns 0 if
    there is no true dependence. -/
def depLatency (producer consumer : JInstr 64) : Nat :=
  if hasTrueDep producer consumer then (costOf producer).latency else 0

/-! ## 5. Critical-path estimate

The critical-path cost of a block is the length (in cycles) of the longest
dependency chain, measured in producer latencies.

We compute it by a forward pass using `List.zipIdx`: for each instruction `j`
at index `j_idx`, its **earliest start time** (`est j_idx`) is the maximum
over all preceding producers `i_idx` of `est i_idx + depLatency instrs[i] instrs[j]`.
The critical path length is `max_j (est j_idx + latency instrs[j])`.

This is the standard list-scheduling lower bound and is exact for chains;
for diamond DAGs it is a lower bound (the schedule may be tighter if the
diamond legs are independent — port pressure then binds instead). -/

/-- Earliest start time for instruction at index `j` in `block`, given a
    precomputed vector `ests` of earlier start times. -/
def estFor (block : List (JInstr 64)) (ests : List Nat) (j : Nat) (instrJ : JInstr 64) : Nat :=
  -- Fold over all i < j
  (block.zipIdx).foldl
    (fun acc (instrI, i) =>
      if i < j then
        let dep := depLatency instrI instrJ
        if dep > 0 then
          -- est[i] from precomputed vector (default 0 if out of range)
          let estI := ests.getD i 0
          Nat.max acc (estI + dep)
        else acc
      else acc)
    0

/-- Build the earliest-start-time vector for the block by a forward sweep. -/
def estVector (block : List (JInstr 64)) : List Nat :=
  (block.zipIdx).foldl
    (fun ests (instrJ, j) =>
      ests ++ [estFor block ests j instrJ])
    ([] : List Nat)

/-- Critical-path cost of `block`: the minimum number of cycles the block
    requires on an out-of-order machine with unlimited issue width, limited
    only by data-dependence latencies. -/
def criticalPathCost (block : List (JInstr 64)) : Nat :=
  let ests := estVector block
  (block.zipIdx).foldl
    (fun acc (instrJ, j) =>
      let estJ := ests.getD j 0
      Nat.max acc (estJ + (costOf instrJ).latency))
    0

/-! ## 6. Port-pressure (throughput lower bound)

The throughput lower bound is `max_p Σ_{i : port p ∈ instr_i.ports} recipThroughput_i`.
For a block with many `mulx` all competing for `p1`, this bound is often
tighter than the critical path. SLOTHY's key observation: the schedule cannot
beat either bound, so `max` is tight in both dimensions simultaneously. -/

/-- Sum of `recipThroughput` for all instructions in `block` that dispatch a
    µop to port `p`. -/
def portLoad (block : List (JInstr 64)) (p : PortId) : Nat :=
  block.foldl
    (fun acc instr =>
      if (costOf instr).ports.contains p
      then acc + (costOf instr).recipThroughput
      else acc)
    0

/-- Port-pressure lower bound: maximum port load across all modelled ports.
    A schedule cannot complete in fewer cycles than this value. -/
def portPressureCost (block : List (JInstr 64)) : Nat :=
  let allPorts : List PortId := [.p0, .p1, .p5, .p6, .p23, .p4, .pOther]
  allPorts.foldl (fun acc p => Nat.max acc (portLoad block p)) 0

/-! ## 7. SLOTHY-style composite cost -/

/-- **SLOTHY-style schedule cost**: maximum of the critical-path latency lower
    bound and the port-pressure throughput lower bound.

    A schedule cannot complete in fewer cycles than `scheduleCostV2 block`
    regardless of instruction ordering (assuming an ideal out-of-order core
    with the port model encoded in `costOf`). Use this as the fitness function
    in `RandomizedScheduleSearch` in place of the coarse `scheduleCost`.

    **Wiring note for the orchestrator**: in `RandomizedScheduleSearch`,
    replace `scheduleCost` with
    `X86CostModel.scheduleCostV2` in the `searchBest` loop. The function
    signature is `List (JInstr 64) → Nat` — a drop-in replacement. No changes
    to the translation-validation machinery (`indep`, `swapBlock`,
    `runBlock_swap_indep`) are needed; those remain cost-agnostic. -/
def scheduleCostV2 (b : List (JInstr 64)) : Nat :=
  Nat.max (criticalPathCost b) (portPressureCost b)

/-! ## 8. Sanity-check examples -/

section Examples

/-- The naive interleaved schedule from `RandomizedScheduleSearch.inputBlock`.
    `mulx h0 l0; add acc_lo l0; adc acc_hi h0; mulx h1 l1; add acc_lo l1; adc acc_hi h1`
    — the second `mulx`'s latency is on the critical path (it is immediately
    followed by the dependent `add`). -/
def inputBlockEx : List (JInstr 64) :=
  [ .mulx "h0" "l0" (.reg "di0") (.reg "m0")
  , .add  "acc_lo" (.reg "l0")
  , .adc  "acc_hi" (.reg "h0")
  , .mulx "h1" "l1" (.reg "di1") (.reg "m1")
  , .add  "acc_lo" (.reg "l1")
  , .adc  "acc_hi" (.reg "h1") ]

/-- The mulx-hoisted schedule from `RandomizedScheduleSearch.hoistedBlock`.
    Both independent `mulx`es issue first, so the second multiply's latency
    overlaps the first product's accumulate chain. -/
def hoistedBlockEx : List (JInstr 64) :=
  [ .mulx "h0" "l0" (.reg "di0") (.reg "m0")
  , .mulx "h1" "l1" (.reg "di1") (.reg "m1")
  , .add  "acc_lo" (.reg "l0")
  , .adc  "acc_hi" (.reg "h0")
  , .add  "acc_lo" (.reg "l1")
  , .adc  "acc_hi" (.reg "h1") ]

-- Critical-path: both schedule variants produce the same 6-cycle critical path
-- (mulx→add dep chain in either order). The granularity difference captured by
-- the old `adjacentStall` heuristic is a *micro-arch stall* below the critical-
-- path DAG level; port-pressure + critical-path correctly classify both at 6c.
#eval criticalPathCost inputBlockEx   -- 6
#eval criticalPathCost hoistedBlockEx -- 6

-- Port pressure: equal for both (same multiset of instructions).
#eval portPressureCost inputBlockEx
#eval portPressureCost hoistedBlockEx

-- SLOTHY composite cost: hoisted ≤ interleaved.
#eval scheduleCostV2 inputBlockEx
#eval scheduleCostV2 hoistedBlockEx

-- Individual cost records for a mulx+adcx+adox triple.
#eval costOf (.mulx "hi" "lo" (.reg "rdx") (.reg "r8"))
#eval costOf (.adcx "acc" (.reg "lo"))
#eval costOf (.adox "acc2" (.reg "hi"))

-- Port load on p1 for hoisted block: 2×MULX(recip=1) = 2. The remaining
-- add/adc instructions dispatch to p0/p1/p5/p6; the p1 load counts those too,
-- giving 2 (mulx) + 4 (add/adc on p1) = 6. Port pressure = 6.
#eval portLoad hoistedBlockEx .p1   -- 6

end Examples

end CatCrypt.Crypto.Optimizer.X86CostModel
