/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public meta import CatCrypt.Crypto.Optimizer.RandomizedRegAlloc
public import CatCrypt.Crypto.Optimizer.RandomizedRegAlloc
public meta import CatCrypt.Crypto.Optimizer.SpillingRegAlloc
public import CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-!
# Joint schedule + register-allocation search (SLOTHY phase-ordering fix)

SLOTHY (Becker et al.) showed that solving scheduling and register allocation
**separately** produces phase-ordering hazards: a schedule move that looks legal
under the register-dependency graph may be illegal once the register allocator's
name reuse is taken into account.

The BLS CIOS witness (`ScheduleSearchMontMulNtt.bls_search7_breaks_runBlock`)
is the concrete instance: the schedule-only adjacent-swap predicate accepts a
sequence of 7 transpositions, but the `hi`/`lo` scratch registers are reused
across all six MULX iterations, so the sequence corrupts `z[2]`. The
schedule-only check cannot see this because **no single adjacent pair shares the
scratch at the moment it is swapped** — the hazard only appears globally.

The fix is to co-solve scheduling and register allocation as **one** move space
`{permutation × renaming}`. A reorder that needs a fresh register for the
front-loaded column multiply is only reachable as a *joint* move that
simultaneously renames the scratch, and the joint legality predicate checks the
renamed instructions — so the aliasing is visible and the hazard is caught.

## Contents

1. `JointMove` — the combined move type.
2. `applyJoint` — apply rename then permute.
3. `jointLegal` — legality predicate accounting for BOTH schedule dependencies
   (on the renamed instructions) AND rename injectivity (no new aliasing).
4. `#eval` regressions: the `distinctNamesBlock` example showing that
   `schedOnlyLegal` is blind to colliding renames but `jointLegal` is not.
5. `searchJoint` — a heuristic driver over `JointMove`s, parameterised over
   an external cost function so it composes with `X86CostModel` later.

> **`@bench-only`.** The `distinctNamesBlock` `List (JInstr 64)` is a
> search-regression fixture; the module emits no deployed `.s` artifact.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.JointScheduleRegAlloc

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-! ## 1. The joint move type -/

/-- A combined schedule + register-allocation move.
  - `perm` is a permutation of `{0, …, n-1}`: `perm[i] = j` means position `i`
    in the output receives the instruction currently at position `j` in the input.
    Length mismatches are handled by clamping to the identity on out-of-range slots.
  - `rename` is a register renaming `String → String`, applied **before** the
    permutation so the dependency check sees the names the allocator will use. -/
structure JointMove where
  perm   : List Nat
  rename : String → String

/-! ## 2. Applying a joint move -/

/-- Apply a permutation `perm` to a list of instructions: position `i` in the
    output receives instruction `perm[i]` from the input, with fallback to
    position `i` itself for out-of-range indices. -/
def applyPerm (perm : List Nat) (xs : List (JInstr 64)) : List (JInstr 64) :=
  (List.range xs.length).map fun i =>
    match perm[i]?, xs[i]? with
    | some j, dflt =>
        match xs[j]? with
        | some instr => instr
        | none       => dflt.getD (.mov "_oob" (.imm 0))
    | none, some dflt => dflt
    | none, none      => .mov "_oob" (.imm 0)

/-- Apply a `JointMove` to a block: **rename first, then permute**.
    The rename is applied first so the subsequent dependency check (§3) operates
    on the names the allocator will actually use. -/
def applyJoint (mv : JointMove) (block : List (JInstr 64)) : List (JInstr 64) :=
  applyPerm mv.perm (renameBlock mv.rename block)

/-! ## 3. Joint legality

A joint move is legal when:

(a) **Rename injectivity**: `rename` is injective on the block's live names —
    no two distinct virtual names map to the same physical register.  A
    non-injective rename collapses two values onto one register, which can
    create phantom independences that the permutation then exploits.

(b) **No hazard on renamed instructions**: for every pair `(i, j)` with `i < j`
    where the permutation places `i` after `j` in the output (i.e. the instruction
    formerly at position `j` now precedes the one formerly at `i`), there is no
    WAW/WAR/RAW or flag-chain hazard between the **renamed** versions of those two
    instructions.

The schedule-only check (`schedOnlyLegal` / `legalSwap'` in the sibling file)
performs only check (b) on the *unmodified* names.  It misses the case where a
rename collapses two independent virtual names onto the same physical, making a
swap that looked safe suddenly hazardous.  `jointLegal` catches this via (a).
-/

/-- All register names mentioned in a block (read or written), deduplicated. -/
def blockLiveNames (block : List (JInstr 64)) : List String :=
  (block.flatMap fun i => writtenNames i ++ readNames i).eraseDups

/-- Check that `rename` is injective on the block's live names: no two distinct
    virtual names map to the same physical.  This is condition (a) of `jointLegal`.
    Uses `List.Nodup` on the mapped image. -/
def renameInjective (rename : String → String) (block : List (JInstr 64)) : Bool :=
  (blockLiveNames block |>.map rename).Nodup

/-- Does instruction `a` conflict with `b` (WAW / WAR / RAW)?
    Uses `writtenNames`/`readNames` from `SpillingRegAlloc` — the canonical
    full-`JInstr`-set footprint model. -/
def hasHazard (a b : JInstr 64) : Bool :=
  let wa := writtenNames a
  let wb := writtenNames b
  let ra := readNames a
  let rb := readNames b
  wa.any (fun w => wb.contains w) ||   -- WAW
  ra.any (fun r => wb.contains r) ||   -- WAR: a reads what b writes
  wa.any (fun w => rb.contains w)      -- RAW: a writes what b reads

/-- Does instruction `a` write flags (CF / OF)? -/
def writesFlags' : JInstr 64 → Bool
  | .mulx _ _ _ _      => false
  | .mulxMem _ _ _ _ _ => false
  | .mov _ _           => false
  | .loadMem _ _ _     => false
  | .storeMem _ _ _    => false
  | .loadMemIdx _ _ _ _ => false
  | .storeMemIdx _ _ _ _ => false
  | .loadSym _ _       => false
  -- `test` and `cmp` are the flag-only writers: all five flags, no register.
  | .test _ _          => true
  | .cmp _ _           => true
  -- `not_` writes its destination and no flag.
  | .not_ _            => false
  -- `andn` writes all five flags (`PF` undefined).
  | .andn _ _ _        => true
  -- the rotates write `OF` and `CF`, so they are flag writers even though
  -- `SF`/`PF`/`ZF` keep their values.
  | .rol _ _           => true
  | .ror _ _           => true
  -- the BMI2 rotate/shift forms write no flag at all — that is what
  -- distinguishes them from `ror`/`shl`/`shr`/`sar`.
  | .rorx _ _ _        => false
  | .shlx _ _ _        => false
  | .shrx _ _ _        => false
  | .sarx _ _ _        => false
  -- extension moves and `lea` write only their destination register.
  | .movzx _ _ _       => false
  | .movsx _ _ _       => false
  | .lea _ _ _ _ _     => false
  -- `inc`/`dec` write four flags, `clc`/`stc`/`bt`/`btr`/`bts` write `CF`, the
  -- rotates through carry write `OF`/`CF`, and the multiplies, double shifts and
  -- sized test write all five.
  | .inc _ | .dec _ | .clc | .stc | .imulri _ _ _ | .mul _ _ _ | .imulWide _ _ _
  | .shld _ _ _ | .shrd _ _ _ | .rcl _ _ | .rcr _ _ | .testN _ _ _
  | .bt _ _ | .btr _ _ | .bts _ _ => true
  -- `xchg` and the general conditional instructions write no flag.
  | .xchg _ _ | .cmovcc _ _ _ | .setcc _ _ => false
  | _                  => true

/-- Does instruction `b` read flags (carry-in for ADC/SBB/ADCX/ADOX, the carry of
    RCL/RCR, the condition of CMOVcc/SETcc)? -/
def readsFlags' : JInstr 64 → Bool
  | .adc _ _  => true
  | .sbb _ _  => true
  | .adcx _ _ => true
  | .adox _ _ => true
  -- `test` and `cmp` read their two operands, no flag.
  | .test _ _ => false
  | .cmp _ _  => false
  -- the bitwise, rotate, shift, extension and address-computation ops take no
  -- flag input.
  | .not_ _ | .andn _ _ _ => false
  | .rol _ _ | .ror _ _ | .rorx _ _ _ => false
  | .shlx _ _ _ | .shrx _ _ _ | .sarx _ _ _ => false
  | .movzx _ _ _ | .movsx _ _ _ | .lea _ _ _ _ _ => false
  -- the rotates through carry read `CF`; `cmovcc`/`setcc` read their condition.
  | .rcl _ _ | .rcr _ _ | .cmovcc _ _ _ | .setcc _ _ => true
  | .inc _ | .dec _ | .clc | .stc | .xchg _ _ | .imulri _ _ _ | .mul _ _ _
  | .imulWide _ _ _ | .shld _ _ _ | .shrd _ _ _ | .testN _ _ _ | .bt _ _ | .btr _ _
  | .bts _ _ => false
  -- the memory-source carry additions read `CF` resp. `OF`.
  | .adcxMem _ _ _ | .adoxMem _ _ _ => true
  | _         => false

/-- Flag-chain hazard: one writes a flag that the other reads, or both write
    flags (flag-state conflict). -/
def hasFlagHazard (a b : JInstr 64) : Bool :=
  (writesFlags' a && writesFlags' b) ||
  (writesFlags' a && readsFlags' b) ||
  (readsFlags' a && writesFlags' b)

/-- Does the permutation cause position `i` to receive an instruction that was
    **after** position `j` (i.e. `perm[i] > perm[j]`)? -/
def permInverts (perm : List Nat) (i j : Nat) : Bool :=
  match perm[i]?, perm[j]? with
  | some pi, some pj => decide (pi > pj)
  | _, _ => false

/-- **Joint legality** of a `JointMove` on a block.

  (a) Rename is injective on live names.
  (b) For every `(i, j)` with `i < j` where the permutation places `i` after
      `j`, the renamed instructions have no WAW/WAR/RAW or flag-chain hazard.
-/
def jointLegal (block : List (JInstr 64)) (mv : JointMove) : Bool :=
  renameInjective mv.rename block &&
  (let renamed := renameBlock mv.rename block
   let n := renamed.length
   (List.range n).all fun i =>
     (List.range n).all fun j =>
       if i < j && permInverts mv.perm i j then
         match renamed[i]?, renamed[j]? with
         | some a, some b => !hasHazard a b && !hasFlagHazard a b
         | _, _ => true
       else true)

/-! ## 4. Schedule-only legality (for comparison in regressions) -/

/-- Adjacent-swap legality using only the instruction footprints, without regard
    to what rename was applied.  This is the predicate the sibling search uses. -/
def schedOnlyLegal (block : List (JInstr 64)) (i : Nat) : Bool :=
  match block[i]?, block[i+1]? with
  | some a, some b => !hasHazard a b && !hasFlagHazard a b
  | _, _ => false

/-! ## 5. Regression: colliding vs injective rename

The key insight: a schedule-only check on a block with **distinct virtual names**
is blind to whether the allocator will map those names to the same physical.

Block: three instructions using two independent multiply outputs `(hi0,lo0)` and
`(hi1,lo1)`.

    (0) mulx hi0 lo0  a b    writes {hi0, lo0}  reads {a, b}
    (1) mov  tmp  lo0         writes {tmp}        reads {lo0}
    (2) mulx hi1 lo1  c d    writes {hi1, lo1}  reads {c, d}

Schedule-only check at position 1 (adjacent swap of (1) and (2)):
  - `mov` writes {tmp}, reads {lo0}.
  - `mulx` writes {hi1, lo1}, reads {c, d}.
  - No overlap → **legal** under schedule-only check.

Joint check with a **colliding rename** `lo0 → "lo", lo1 → "lo"` (the BLS
allocator pattern):
  - Injectivity check: both `lo0` and `lo1` map to `"lo"` → **not injective**
    → joint check **rejects** the move.

Joint check with an **injective rename** `lo0 → "rax", lo1 → "rbx"`:
  - Injectivity check passes.
  - No hazard between renamed instructions.
  - Joint check **accepts** the move.
-/

/-- A block with distinct virtual names for the two multiplies' outputs. -/
def distinctNamesBlock : List (JInstr 64) :=
  [ .mulx "hi0" "lo0" (.reg "a") (.reg "b")   -- (0) product 0
  , .mov  "tmp" (.reg "lo0")                    -- (1) reads lo0
  , .mulx "hi1" "lo1" (.reg "c") (.reg "d") ]  -- (2) product 1, truly independent

/-- Permutation that swaps positions 1 and 2. -/
def swapPerm12 : List Nat := [0, 2, 1]

/-- Colliding rename: maps both `lo0` and `lo1` to the same physical `"lo"`.
    This is the BLS CIOS allocator pattern — the allocator reuses the scratch
    register `lo` for every column multiply. -/
def collidingRename : String → String
  | "lo0" => "lo"
  | "lo1" => "lo"
  | "hi0" => "hi"
  | "hi1" => "hi"
  | s     => s

/-- Injective rename: maps each virtual to a distinct physical. -/
def injectiveRename : String → String
  | "lo0" => "rax"
  | "lo1" => "rbx"
  | "hi0" => "rcx"
  | "hi1" => "rdx_phys"
  | s     => s

/-- Joint move with the colliding rename + swap 1↔2. -/
def collidingMove : JointMove := { perm := swapPerm12, rename := collidingRename }

/-- Joint move with the injective rename + swap 1↔2. -/
def injectiveMove : JointMove := { perm := swapPerm12, rename := injectiveRename }

-- (1) Schedule-only says LEGAL: the two instructions at positions 1 and 2 have
-- distinct virtual names and disjoint footprints. Expected: `true`.
#eval schedOnlyLegal distinctNamesBlock 1

-- (2) Joint check with COLLIDING rename: rejected because `lo0` and `lo1` both
-- map to `"lo"` — the injectivity check catches the aliasing. Expected: `false`.
#eval jointLegal distinctNamesBlock collidingMove

-- (3) Joint check with INJECTIVE rename: accepted — injective, no hazard. Expected: `true`.
#eval jointLegal distinctNamesBlock injectiveMove

/-! ## 6. The heuristic search driver -/

/-- LCG step (same constants as `RandomizedScheduleSearch` and `RandomizedRegAlloc`). -/
def lcgNext (s : UInt32) : UInt32 := s * 1664525 + 1013904223

/-- Fisher–Yates shuffle of `{0, …, n-1}` with seed. Returns `(perm, nextSeed)`. -/
def randomPerm (n : Nat) (seed : UInt32) : List Nat × UInt32 :=
  let rec go (s : UInt32) (rem acc : List Nat) (fuel : Nat) :
      List Nat × UInt32 :=
    match fuel, rem with
    | 0, _  => (acc ++ rem, s)
    | _, [] => (acc, s)
    | fuel+1, _ =>
      let s' := lcgNext s
      let k  := s'.toNat % rem.length
      match rem[k]? with
      | none   => (acc ++ rem, s')
      | some x => go s' (acc ++ [x]) (rem.eraseIdx k) fuel
  go seed [] (List.range n) n

/-- The free physical pool a block's non-`pinned` names may be renamed into:
    `AsmPrinter.gpPool` minus the registers `pinned` already occupies. This is the
    same pool `RandomizedRegAlloc.searchAssign`/`AsmPrinter.allocGp` draw from, so
    a rename built over it is one `RandomizedRegAlloc.accept` can adjudicate. -/
def freePool (pinned : GpAlloc) : List String :=
  let used := pinned.map Prod.snd
  gpPool.filter (fun r => ¬ used.contains r)

/-- The `GpAlloc` (name ↦ physical association list) a `rename` induces on a
    block's live names — the form `RandomizedRegAlloc.accept` consumes. -/
def renameToAlloc (rename : String → String) (block : List (JInstr 64)) : GpAlloc :=
  (blockLiveNames block).map (fun n => (n, rename n))

/-- Generate a random injective rename from the block's live names by drawing,
    without replacement, from the **real GP register pool** (`AsmPrinter.gpPool`,
    minus the `pinned` physicals) rather than the former synthetic `_r<k>`
    suffix-space. `RandomizedRegAlloc.shuffle` seeds the draw, exactly as
    `searchAssign` does, so the produced rename is a candidate
    `RandomizedRegAlloc.accept` can adjudicate for GP-overflow safety. Names
    beyond the free pool (a GP-overflow) keep their original name — `accept`'s
    `allocOverflow = none` clause then rejects the move upstream. Returns
    `(rename, nextSeed)`. -/
def randomInjectiveRename (pinned : GpAlloc) (block : List (JInstr 64))
    (seed : UInt32) : (String → String) × UInt32 :=
  let names := blockLiveNames block
  let pool  := shuffle seed (freePool pinned)
  let assign : List (String × String) := names.zip pool
  let ren : String → String := fun s => (assign.lookup s).getD s
  (ren, lcgNext seed)

/-- Try one joint move: generate a random permutation and a GP-pool injective
    rename, accept if **both** legality gates pass and the cost decreases. The
    two gates are independent and both required:
    - `jointLegal` is the schedule + rename-injectivity dependency check (§3);
    - `RandomizedRegAlloc.accept [] (renameToAlloc ren block) block` is the
      GP-overflow / physical-distinctness guard — it rejects any rename that
      would spill past `AsmPrinter.gpPool` or alias two virtuals onto one
      physical (the #380 collision). Only moves passing both are candidates;
      the chosen winner is still TV-gated downstream (the joint search only
      *widens* the candidate space, never bypasses translation validation). -/
def searchJointStep
    (cost : List (JInstr 64) → Nat)
    (block : List (JInstr 64)) (bestCost : Nat) (seed : UInt32) :
    List (JInstr 64) × Nat × UInt32 :=
  let n := block.length
  let (perm, seed1) := randomPerm n seed
  let (ren, seed2)  := randomInjectiveRename [] block seed1
  let mv : JointMove := { perm := perm, rename := ren }
  if jointLegal block mv && accept [] (renameToAlloc ren block) block then
    let cand := applyJoint mv block
    let c    := cost cand
    if c < bestCost then (cand, c, seed2)
    else (block, bestCost, seed2)
  else
    (block, bestCost, seed2)

/-- Run `iters` joint-search steps from `block`, optimising `cost`.
    The cost function is a **parameter** so this driver composes with
    `X86CostModel.scheduleCostV2` without importing it.
    Returns the best block found and its cost. -/
def searchJoint
    (iters : Nat)
    (cost : List (JInstr 64) → Nat)
    (block : List (JInstr 64))
    (seed : UInt32) :
    List (JInstr 64) × Nat :=
  let rec go (n : Nat) (b : List (JInstr 64)) (bestC : Nat) (s : UInt32) :
      List (JInstr 64) × Nat :=
    match n with
    | 0     => (b, bestC)
    | n + 1 =>
      let (b', c', s') := searchJointStep cost b bestC s
      go n b' c' s'
  go iters block (cost block) seed

/-! ## 7. Orchestrator wiring notes

To plug `searchJoint` into the live pipeline:

1. **Cost function**: pass `RandomizedScheduleSearch.scheduleCost` or
   `X86CostModel.scheduleCostV2` as the `cost` argument.  `searchJoint` imports
   neither — the dependency is injected at call sites.

2. **Integration point**: after `RandomizedScheduleSearch.searchBest` produces a
   candidate, if translation validation (TV) *rejects* it (as it does for the BLS
   block — `bls_search7_breaks_runBlock`), feed the original block to `searchJoint`
   instead, with a cost that accounts for both latency and register pressure.  The
   joint search explores moves the schedule-only search cannot reach.

3. **Physical register pool**: `randomInjectiveRename` draws from
   `AsmPrinter.gpPool` (seeded by `RandomizedRegAlloc.shuffle`), and
   `searchJointStep` gates every candidate with `RandomizedRegAlloc.accept` so a
   rename that overflows the GP pool or aliases two virtuals onto one physical is
   rejected before it can be a winner.

4. **TV of the winner**: feed the winner of `searchJoint` through
   `runBlock`-equality or `lowerBlock_denote_closed` (the same TV gate the sibling
   search uses).  Only TV-passing winners may be emitted; the joint search widens
   the reachable candidate space, but TV remains the soundness gate.
-/

end CatCrypt.Crypto.Optimizer.JointScheduleRegAlloc
