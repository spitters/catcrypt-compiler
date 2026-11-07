/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFootprint
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFootprint
public import CatCrypt.Crypto.Optimizer.X86CostModel
public meta import CatCrypt.Crypto.Optimizer.X86CostModel

/-!
# An order-dependent schedule cost: list scheduling on a Zen 4 port model

`zen4Cost block` is the finishing cycle of `block` under a list scheduler over the integer
core of AMD Zen 4. The instructions are taken in program order. Each is dispatched in program
order, at most six macro-ops per cycle; it issues at the first cycle at or after its dispatch
cycle at which its operands are ready and each of its resource uses finds a free unit of its
class; its results are ready `lat` cycles after issue. A unit taken by an earlier instruction
is not available to a later one, and a later instruction may take a unit at a cycle before an
earlier instruction's issue cycle (out-of-order issue, oldest first). The cost therefore
depends on the order of the block: the dispatch cycle of an instruction is its position
divided by the dispatch width, and the units an instruction finds free depend on the
instructions before it. `X86CostModel.scheduleCostV2`, the maximum of the dependence-graph
critical path and the port load, does not change under a reorder that keeps the dependences
(`zen4Cost_order_dependent` exhibits a legal swap that changes `zen4Cost` and keeps
`scheduleCostV2`).

Dependences are read off the footprints of `JInstrFootprint` (registers, the five flags and
memory cells), so an `adc` waits for the carry of the instruction before it and a load waits
for a store to its cell. Write-after-read and write-after-write orders on registers and flags
do not delay an instruction, since the core renames both; the reader of a location waits for
the most recent earlier writer of an overlapping location.

## Main definitions

* `zen4Cost`: the finishing cycle of a block under the list scheduler of the Zen 4 table.
* `zen4Op`: the macro-ops, latency and unit uses of each form of `JInstr 64`.
* `zen4Cost_order_dependent`: a swap certified by `checkSwapF` that lowers `zen4Cost` and
  keeps `X86CostModel.scheduleCostV2`.

## The table and its source

`zen4Op` is the only latency and resource table of the model. It transcribes the LLVM
scheduling model of Zen 4, `llvm/lib/Target/X86/X86ScheduleZnver4.td` at tag
`llvmorg-18.1.8`, as `llvm-mca-18 -mcpu=znver4 -instruction-info -resource-pressure` reports
it for each instruction form the printer emits: number of macro-ops, latency, and the
resource units held with their cycles. That file states that it follows the *AMD Software
Optimization Guide for AMD Family 19h Processors* (publication 56665). The uops.info and
Agner Fog tables were not reachable when the table was written; a refresh against them should
replace the rows here and nowhere else. Resource classes: `alu` (ALU0 to ALU3), `mul` (ALU1,
the multiplier), `alu12` (shifts, rotates, bit tests), `alu03` (conditional moves and
`setcc`), `agu` (three address generators), `lsu` (three load-store pipes) and `st` (two store
units).

## What the model omits

The front end (fetch, decode, the op cache) and branches; the capacity of the scheduler
queues and of the 320-entry retire window, and retirement; register-file and flag-renaming
limits; partial-register merges; macro-op fusion; the extra cycle of a complex address;
store-to-load forwarding (a load of a cell written by an earlier store waits for the store's
latency plus its own); memory disambiguation and cache misses (every load hits the L1 cache);
and aliasing between cells of different base names, which `runBlock` treats as distinct. Two
cycle counts of the LLVM model are kept although they read as throughput encodings rather
than occupancies: `adc`, `sbb`, `adcx` and `adox` hold one ALU for four cycles, and a move of
an immediate holds one ALU for two.

The module takes about 1.5 s to elaborate, most of it the `native_decide` of
`zen4Cost_order_dependent`, which compiles the scheduler.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Zen4ListSchedule

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFootprint
open CatCrypt.Crypto.SecureCompilation.X86Backend.RescheduleEquivalence (applySwap)

/-! ## 1. Units, uses and the table -/

/-- The execution units of the Zen 4 integer core that the table names. -/
inductive ExecUnit where
  | alu0 | alu1 | alu2 | alu3
  | agu0 | agu1 | agu2
  | lsu0 | lsu1 | lsu2
  | st0 | st1
  deriving DecidableEq, Repr

/-- Any ALU. -/
def alu : List ExecUnit := [.alu0, .alu1, .alu2, .alu3]
/-- The multiplier, on ALU1. -/
def mul : List ExecUnit := [.alu1]
/-- ALU1 and ALU2: shifts, rotates, bit tests. -/
def alu12 : List ExecUnit := [.alu1, .alu2]
/-- ALU0 and ALU3: conditional moves and `setcc`. -/
def alu03 : List ExecUnit := [.alu0, .alu3]
/-- The address generators. -/
def agu : List ExecUnit := [.agu0, .agu1, .agu2]
/-- The load-store pipes. -/
def lsu : List ExecUnit := [.lsu0, .lsu1, .lsu2]
/-- The store units. -/
def st : List ExecUnit := [.st0, .st1]

/-- One resource use: a unit of the class `units`, held for `cycles` cycles from issue. -/
structure Use where
  units : List ExecUnit
  cycles : Nat
  deriving Repr

/-- The cost record of one instruction: macro-ops dispatched, latency of its results, the
    latency of the high result of a widening multiply (`latHi`, equal to `lat` elsewhere),
    whether it is a zero idiom that reads no operand, and its resource uses. -/
structure OpCost where
  uops : Nat
  lat : Nat
  latHi : Nat
  zeroIdiom : Bool := false
  uses : List Use
  deriving Repr

/-- A one-macro-op instruction with one latency. -/
def op1 (lat : Nat) (uses : List Use) : OpCost := ⟨1, lat, lat, false, uses⟩

/-- **The Zen 4 table** (LLVM `X86ScheduleZnver4.td`, `llvmorg-18.1.8`, as reported by
    `llvm-mca-18 -mcpu=znver4`). One row per form of `JInstr 64`. -/
def zen4Op : JInstr 64 → OpCost
  -- `mov r, r` is eliminated at rename; `mov r, imm` holds one ALU for two cycles.
  | .mov _ (.reg _) => ⟨1, 0, 0, false, []⟩
  | .mov _ (.imm _) => op1 1 [⟨alu, 2⟩]
  -- `xor r, r` on one register is a zero idiom: no unit, no operand.
  | .xor_ d (.reg r) => if d = r then ⟨1, 0, 0, true, []⟩ else op1 1 [⟨alu, 1⟩]
  | .xor_ _ (.imm _) => op1 1 [⟨alu, 1⟩]
  | .add _ _ | .sub _ _ | .and_ _ _ | .or_ _ _ | .neg _ | .not_ _ | .test _ _ | .cmp _ _
  | .andn _ _ _ | .movzx _ _ _ | .movsx _ _ _ | .inc _ | .dec _ | .clc | .stc
  | .testN _ _ _ => op1 1 [⟨alu, 1⟩]
  -- the carry additions (`WriteADC`): one ALU, four cycles.
  | .adc _ _ | .sbb _ _ | .adcx _ _ | .adox _ _ => op1 1 [⟨alu, 4⟩]
  | .imul _ _ | .imulri _ _ _ => op1 3 [⟨mul, 1⟩]
  | .rol _ _ | .ror _ _ | .shl _ _ | .shr _ _ | .sar _ _ | .rorx _ _ _ | .shlx _ _ _
  | .shrx _ _ _ | .sarx _ _ _ | .bzhi _ _ _ | .bt _ _ => op1 1 [⟨alu12, 1⟩]
  | .rcl _ _ | .rcr _ _ => op1 1 [⟨alu12, 2⟩]
  | .btr _ _ | .bts _ _ => ⟨2, 2, 2, false, [⟨alu12, 2⟩]⟩
  | .shld _ _ _ | .shrd _ _ _ => ⟨4, 2, 2, false, [⟨alu12, 3⟩]⟩
  -- `lea base + idx * scale + off` is the complex form: two macro-ops, latency two.
  | .lea _ _ _ _ _ => ⟨2, 2, 2, false, [⟨alu, 1⟩]⟩
  | .cmove _ _ | .cmovne _ _ | .cmovb _ _ | .cmovcc _ _ _ => op1 1 [⟨alu03, 1⟩]
  | .setc _ | .setcc _ _ => op1 1 [⟨alu03, 2⟩]
  -- `mulx`: the low result after three cycles, the high one after four.
  | .mulx _ _ _ _ => ⟨2, 3, 4, false, [⟨mul, 1⟩]⟩
  | .mulxMem _ _ _ _ _ => ⟨2, 7, 8, false, [⟨agu, 1⟩, ⟨mul, 1⟩, ⟨lsu, 1⟩]⟩
  | .mul _ _ _ | .imulWide _ _ _ => ⟨2, 3, 3, false, [⟨mul, 3⟩]⟩
  | .loadMem _ _ _ | .loadMemIdx _ _ _ _ => op1 5 [⟨agu, 1⟩, ⟨lsu, 1⟩]
  | .storeMem _ _ _ | .storeMemIdx _ _ _ _ => op1 1 [⟨agu, 1⟩, ⟨lsu, 2⟩, ⟨st, 2⟩]
  | .loadSym _ _ => op1 1 [⟨agu, 1⟩]
  | .xchg _ _ => ⟨2, 0, 0, false, []⟩
  | .addMem _ _ _ | .aluMem _ _ _ _ | .cmpMem _ _ _ | .andnMem _ _ _ _ =>
      op1 5 [⟨agu, 1⟩, ⟨alu, 1⟩, ⟨lsu, 1⟩]
  | .addToMem _ _ _ => op1 6 [⟨agu, 2⟩, ⟨alu, 1⟩, ⟨lsu, 2⟩, ⟨st, 1⟩]
  | .adcxMem _ _ _ | .adoxMem _ _ _ => op1 5 [⟨agu, 1⟩, ⟨alu, 4⟩, ⟨lsu, 1⟩]
  | .imulMem _ _ _ | .imulriMem _ _ _ _ => op1 7 [⟨agu, 1⟩, ⟨mul, 1⟩, ⟨lsu, 1⟩]
  | .cmovccMem _ _ _ _ => op1 5 [⟨agu, 1⟩, ⟨alu03, 1⟩, ⟨lsu, 1⟩]

/-- The dispatch width: macro-ops per cycle. -/
def dispatchWidth : Nat := 6

/-! ## 2. The list scheduler -/

/-- The state of the scheduler after a prefix of the block. -/
structure SchedState where
  /-- The current dispatch cycle and the macro-ops already dispatched in it. -/
  disp : Nat
  slots : Nat
  /-- The cycle at which each written location is ready, most recent first. -/
  ready : List (Loc × Nat)
  /-- The reservations `(unit, first cycle, cycle after the last)`. -/
  busy : List (ExecUnit × Nat × Nat)
  /-- The latest completion cycle. -/
  finish : Nat
  deriving Repr

/-- The cycle at which the value at `l` is ready: that of the most recent earlier write of
    an overlapping location, `0` for a value live at entry. -/
def readyAt (ready : List (Loc × Nat)) (l : Loc) : Nat :=
  match ready.find? (fun p => p.1.overlap l) with
  | some p => p.2
  | none => 0

/-- Unit `u` is free over the cycles `[t, t + c)`. -/
def unitFree (busy : List (ExecUnit × Nat × Nat)) (u : ExecUnit) (t c : Nat) : Bool :=
  busy.all fun (v, a, b) => v != u || b ≤ t || t + c ≤ a

/-- Reserve one unit for each use at cycle `t`, the first free unit of each class, or fail. -/
def reserve (busy : List (ExecUnit × Nat × Nat)) (t : Nat) :
    List Use → Option (List (ExecUnit × Nat × Nat))
  | [] => some busy
  | u :: us =>
      match u.units.find? (fun v => unitFree busy v t u.cycles) with
      | some v => reserve ((v, t, t + u.cycles) :: busy) t us
      | none => none

/-- The first cycle from `t` on, within `fuel` cycles, at which every use finds a unit. -/
def issueFrom (busy : List (ExecUnit × Nat × Nat)) (uses : List Use) :
    Nat → Nat → Nat × List (ExecUnit × Nat × Nat)
  | t, 0 => (t, busy)
  | t, fuel + 1 =>
      match reserve busy t uses with
      | some busy' => (t, busy')
      | none => issueFrom busy uses (t + 1) fuel

/-- The latency of the result of `i` at the written location `l`: `latHi` at the high
    destination of a widening multiply, `lat` elsewhere. -/
def latAt (i : JInstr 64) (c : OpCost) (l : Loc) : Nat :=
  match i with
  | .mulx dh _ _ _ | .mulxMem dh _ _ _ _ => if l = .reg dh then c.latHi else c.lat
  | _ => c.lat

/-- One step of the scheduler. -/
def listScheduleStep (st : SchedState) (i : JInstr 64) : SchedState :=
  let c := zen4Op i
  let (disp, slots) :=
    if st.slots + c.uops ≤ dispatchWidth then (st.disp, st.slots + c.uops)
    else (st.disp + 1, c.uops)
  let reads := if c.zeroIdiom then [] else rdLocs i
  let opReady := reads.foldl (fun a l => max a (readyAt st.ready l)) 0
  let earliest := max disp opReady
  let fuel := st.busy.foldl (fun a (_, x, y) => a + (y - x)) 0 + 1
  let (t, busy) := issueFrom st.busy c.uses earliest fuel
  let writes := wrLocs i
  let ready := writes.foldl (fun acc l => (l, t + latAt i c l) :: acc) st.ready
  let done := writes.foldl (fun a l => max a (t + latAt i c l)) (t + 1)
  { disp, slots, ready, busy, finish := max st.finish done }

/-- **The order-dependent cost**: the finishing cycle of the block under the list scheduler
    of the Zen 4 table. -/
def zen4Cost (block : List (JInstr 64)) : Nat :=
  (block.foldl listScheduleStep ⟨0, 0, [], [], 0⟩).finish

/-! ## 3. The cost depends on the order -/

-- @bench-only: `orderWitness` is a fixture for the theorem below; this module emits no `.s`.
/-- Six independent additions followed by a multiply whose low result feeds an addition. -/
def orderWitness : List (JInstr 64) :=
  [ .add "a0" (.reg "b0"), .add "a1" (.reg "b1"), .add "a2" (.reg "b2")
  , .add "a3" (.reg "b3"), .add "a4" (.reg "b4"), .add "a5" (.reg "b5")
  , .mulx "h" "l" (.reg "x") (.reg "y"), .add "c" (.reg "l") ]

/-- **The cost depends on the order.** Transposing the multiply with the addition before it is
    a certified swap (`checkSwapF`); in the swapped order the multiply finds the multiplier
    free one cycle earlier, which lowers `zen4Cost`. The out-of-order bound `scheduleCostV2`
    of the two orders is the same. -/
theorem zen4Cost_order_dependent :
    checkSwapF 5 orderWitness = true ∧
    zen4Cost (applySwap 5 orderWitness) < zen4Cost orderWitness ∧
    X86CostModel.scheduleCostV2 (applySwap 5 orderWitness)
      = X86CostModel.scheduleCostV2 orderWitness := by
  native_decide

end CatCrypt.Crypto.Optimizer.Zen4ListSchedule
