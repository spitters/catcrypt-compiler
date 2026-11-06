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
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFootprint
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFootprint

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
   (the footprint independence `JInstrFootprint.indepF` of every pair of renamed input
   instructions whose order the permutation inverts) AND rename injectivity.
4. `#eval` regressions: the `distinctNamesBlock` example showing that
   `schedOnlyLegal` is blind to colliding renames but `jointLegal` is not.
5. `searchJointSegs`, `searchJoint` — the search over a block of segments: a move is the
   transposition of two adjacent segments with independent footprints
   (`JInstrFootprint.checkSwapSeg`) or the renaming of one name outside the pinned names
   to a register of `gpPool` that the block does not use, ranked by an external cost.
   A segment is the machine image of one instruction of a printed body, or one
   instruction (`searchJoint`).

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFootprint (indepF runBlock_swapSeg)

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
  | .xchg _ _ | .cmovcc _ _ _ | .cmovccMem _ _ _ _ | .setcc _ _ => false
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
  | .rcl _ _ | .rcr _ _ | .cmovcc _ _ _ | .cmovccMem _ _ _ _ | .setcc _ _ => true
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
  (b) For every pair of output positions `i < j` whose instructions the permutation takes
      from input positions `perm[i] > perm[j]`, the renamed input instructions at
      `perm[j]` and `perm[i]` have independent footprints (`JInstrFootprint.indepF`).

  An earlier version compared the instructions at the input positions `i` and `j`
  themselves instead of the positions `perm[i]` and `perm[j]` the permutation moves, and
  used the register-only hazard `hasHazard`, which reads no memory footprint. -/
def jointLegal (block : List (JInstr 64)) (mv : JointMove) : Bool :=
  renameInjective mv.rename block &&
  (let renamed := renameBlock mv.rename block
   let n := renamed.length
   (List.range n).all fun i =>
     (List.range n).all fun j =>
       if i < j then
         match mv.perm[i]?, mv.perm[j]? with
         | some pi, some pj =>
             if pj < pi then
               match renamed[pj]?, renamed[pi]? with
               | some a, some b => indepF a b
               | _, _ => true
             else true
         | _, _ => true
       else true)

/-! ## 4. Schedule-only legality (for comparison in regressions) -/

/-- Adjacent-swap legality using only the instruction footprints, without regard
    to what rename was applied.  This is the predicate the sibling search uses. -/
def schedOnlyLegal (block : List (JInstr 64)) (i : Nat) : Bool :=
  match block[i]?, block[i+1]? with
  | some a, some b => indepF a b
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

/-! ### The search over segments

The moves are local. A random permutation of a block of a hundred instructions inverts a
dependent pair with probability close to one, so a step that draws a whole permutation
almost never proposes a legal move; the step below draws a position and transposes two
adjacent segments, or renames one name. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFootprint
  (checkSwapSeg swapSeg indepSeg)

/-- A move of the segment search. -/
inductive SegMove where
  /-- Transpose the segments at `k` and `k + 1`. -/
  | swap (k : Nat)
  /-- Exchange the names `r` and `f` throughout the block. -/
  | rename (r f : String)
  deriving DecidableEq, Repr

/-- The transposition of two names, an injective renaming. -/
def swapName (r f : String) (x : String) : String :=
  if x = r then f else if x = f then r else x

theorem swapName_injective (r f : String) : Function.Injective (swapName r f) := by
  intro x y h
  simp only [swapName] at h
  split_ifs at h <;> grind

/-- The names of a block of segments. -/
def segNames (segs : List (List (JInstr 64))) : List String :=
  blockLiveNames segs.flatten

/-- The renamings available on a block: a name outside `pinned` paired with a register of
    `gpPool` that the block does not use. -/
def renameCands (pinned : List String) (segs : List (List (JInstr 64))) :
    List String × List String :=
  let names := segNames segs
  (names.filter fun n => !pinned.contains n, gpPool.filter fun r => !names.contains r)

/-- Apply a move, or `none` when it is not legal. -/
def applySegMove (pinned : List String) (segs : List (List (JInstr 64))) :
    SegMove → Option (List (List (JInstr 64)))
  | .swap k => if checkSwapSeg k segs then some (swapSeg k segs) else none
  | .rename r f =>
      let (rs, fs) := renameCands pinned segs
      if rs.contains r && fs.contains f then some (segs.map (renameBlock (swapName r f)))
      else none

/-- Draw a move: with probability one in eight a renaming, otherwise a transposition at a
    random position. Returns the move and the next seed. -/
def drawSegMove (pinned : List String) (segs : List (List (JInstr 64))) (seed : UInt32) :
    Option SegMove × UInt32 :=
  let s1 := lcgNext seed
  let s2 := lcgNext s1
  if s1.toNat % 8 = 0 then
    let (rs, fs) := renameCands pinned segs
    match rs[s2.toNat % (rs.length + 1)]?, fs[(lcgNext s2).toNat % (fs.length + 1)]? with
    | some r, some f => (some (.rename r f), lcgNext s2)
    | _, _ => (none, lcgNext s2)
  else (some (.swap (s2.toNat % max 1 (segs.length - 1))), s2)

/-- The state of the segment search: the current block, its cost, the moves applied so
    far (newest first), the best block seen with its cost, and the seed. -/
structure SegSearch where
  cur : List (List (JInstr 64))
  cost : Nat
  log : List SegMove
  best : List (List (JInstr 64))
  bestCost : Nat
  seed : UInt32

/-- One step of the segment search: draw a move; apply it when it is legal and the cost
    of the result does not exceed the current cost. -/
def segSearchStep (cost : List (JInstr 64) → Nat) (pinned : List String) (st : SegSearch) :
    SegSearch :=
  let (mv?, seed') := drawSegMove pinned st.cur st.seed
  match mv? with
  | none => { st with seed := seed' }
  | some mv =>
      match applySegMove pinned st.cur mv with
      | none => { st with seed := seed' }
      | some cand =>
          let c := cost cand.flatten
          if c ≤ st.cost then
            let better := c < st.bestCost
            { cur := cand, cost := c, log := mv :: st.log,
              best := if better then cand else st.best,
              bestCost := if better then c else st.bestCost, seed := seed' }
          else { st with seed := seed' }

/-- The initial state of the segment search. -/
def segSearchInit (cost : List (JInstr 64) → Nat) (segs : List (List (JInstr 64)))
    (seed : UInt32) : SegSearch :=
  let c := cost segs.flatten
  ⟨segs, c, [], segs, c, seed⟩

/-- Run `iters` steps of the segment search. -/
def segSearchRun (cost : List (JInstr 64) → Nat) (pinned : List String) :
    Nat → SegSearch → SegSearch
  | 0, st => st
  | n + 1, st => segSearchRun cost pinned n (segSearchStep cost pinned st)

/-- **The joint search over segments**: `iters` steps from `segs` with seed `seed`; the best
    block seen, its cost, and the moves applied (oldest first). The cost is a parameter, so
    the driver composes with `Zen4ListSchedule.zen4Cost` without importing it. -/
def searchJointSegs (iters : Nat) (cost : List (JInstr 64) → Nat) (pinned : List String)
    (segs : List (List (JInstr 64))) (seed : UInt32) :
    List (List (JInstr 64)) × Nat × List SegMove :=
  let st := segSearchRun cost pinned iters (segSearchInit cost segs seed)
  (st.best, st.bestCost, st.log.reverse)

/-- **The joint search** on a block of single instructions, with no pinned name. Returns the
    best block found and its cost. -/
def searchJoint (iters : Nat) (cost : List (JInstr 64) → Nat) (block : List (JInstr 64))
    (seed : UInt32) : List (JInstr 64) × Nat :=
  let (b, c, _) := searchJointSegs iters cost [] (block.map fun i => [i]) seed
  (b.flatten, c)

/-- A transposition the search applies preserves `runBlock` of the block; a renaming is
    the injective `swapName r f`, under which `RandomizedRegAlloc.regalloc_runBlock_sound`
    relates the runs. -/
theorem applySegMove_swap_runBlock (s : JState 64) (pinned : List String)
    (segs segs' : List (List (JInstr 64))) (k : Nat)
    (h : applySegMove pinned segs (.swap k) = some segs') :
    runBlock s segs'.flatten = runBlock s segs.flatten := by
  simp only [applySegMove] at h
  split at h
  · rename_i hk
    obtain rfl := Option.some.inj h
    exact runBlock_swapSeg s k segs hk
  · cases h

/-- On a log of transpositions only, the block the moves reach runs to the same state as the
    input, on every state. -/
theorem applySegMoves_swaps_runBlock (s : JState 64) (pinned : List String) :
    ∀ (log : List SegMove) (segs segs' : List (List (JInstr 64))),
      (∀ mv ∈ log, ∃ k, mv = .swap k) →
      log.foldlM (applySegMove pinned) segs = some segs' →
      runBlock s segs'.flatten = runBlock s segs.flatten
  | [], segs, segs', _, h => by
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
      rw [h]
  | mv :: log, segs, segs', hs, h => by
      obtain ⟨k, rfl⟩ := hs mv List.mem_cons_self
      simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨mid, hmid, hrest⟩ := h
      rw [applySegMoves_swaps_runBlock s pinned log mid segs'
        (fun m hm => hs m (List.mem_cons_of_mem _ hm)) hrest]
      exact applySegMove_swap_runBlock s pinned segs mid k hmid

/-! ## 7. Orchestrator wiring notes

To plug `searchJoint` into the live pipeline:

1. **Cost function**: pass `Zen4ListSchedule.zen4Cost` as the `cost` argument; it
   depends on the order of the block. `searchJoint` does not import it — the
   dependency is injected at call sites.

2. **Integration point**: after `RandomizedScheduleSearch.searchBest` produces a
   candidate, if translation validation (TV) *rejects* it (as it does for the BLS
   block — `bls_search7_breaks_runBlock`), feed the original block to `searchJoint`
   instead, with a cost that accounts for both latency and register pressure.  The
   joint search explores moves the schedule-only search cannot reach.

3. **Physical register pool**: a renaming move exchanges a name outside the pinned
   names with a register of `AsmPrinter.gpPool` that the block does not use, an
   injective renaming. On a block that uses every register of the pool there is no
   renaming move.

4. **TV of the winner**: feed the winner of `searchJoint` through
   `runBlock`-equality or `lowerBlock_denote_closed` (the same TV gate the sibling
   search uses).  Only TV-passing winners may be emitted; the joint search widens
   the reachable candidate space, but TV remains the soundness gate.
-/

end CatCrypt.Crypto.Optimizer.JointScheduleRegAlloc
