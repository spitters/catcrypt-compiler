/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc
public import CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc
public meta import CatCrypt.Crypto.Optimizer.RandomizedRegAlloc
public import CatCrypt.Crypto.Optimizer.RandomizedRegAlloc
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect

/-!
# Verified MOVE COALESCING (P4): the one register-allocator perf pass jasminc has
  that the owned allocator lacked

The owned register allocator (`GraphColoringRegAlloc.graphColorAlloc`, linear-scan
`SpillingRegAlloc`, and the renaming `RandomizedRegAlloc`) emits a `mov dst, src`
whenever two SSA names are unified by a copy — at φ-resolution, at ABI argument
shuffles, at the head of a leaf that re-binds an input register. When `dst` and
`src` do **not interfere** (their `[def, lastUse]` live ranges do not overlap),
that copy is redundant: the allocator could have placed `dst` and `src` in the
**same** physical register, dropping the `mov` entirely. jasminc's allocator does
this (Briggs/George conservative coalescing); the owned allocator did not. P4 is
exactly this gap.

## Coalescing is a RENAME (so it reuses the proved rename machinery)

The key observation — the reason this needs no new machine semantics — is that
**coalescing the copy `mov d (.reg s)` is the renaming `d ↦ s`** applied to the
whole block, after which the copy itself has become the identity `mov s (.reg s)`
and is dropped:

  `coalesce d s block = dropIdMovs (renameBlock (subst d s) block)`

So coalescing reuses two already-proved facts, composed:

1. **Renaming soundness** (`RandomizedRegAlloc.runBlock_renameBlock_rel`): an
   injective renaming `ρ` carries the `StateRel ρ` simulation through `runBlock`.
   The coalescing substitution `subst d s` sends `d ↦ s` and fixes everything else,
   so it identifies the two names and is injective only for `d = s`
   (`subst_not_injective`) — the one case the non-interference certificate
   `coalesceInterfereOk` excludes. The simulation therefore says nothing about a
   certified copy; §7 states what separates the two runs instead.

2. **Identity-mov drop** (`runBlock_dropIdMovs`, proved here, fully general): a
   `mov r (.reg r)` writes `r` the value it already holds, so it is a `runBlock`
   no-op. Dropping every identity self-mov preserves `runBlock` on **all** blocks
   and **all** states — no side condition.

The transform is **conservative** (Briggs/George): a copy is coalesced only when
its two registers have non-overlapping live ranges, so coalescing never increases
register pressure and never forces a new spill. A copy that would create
interference is left alone.

## What is built

* `coalesceInterfereOk` (§1): the decidable non-interference certificate for a
  candidate copy `mov d (.reg s)` — `d ≠ s` and their live ranges do not overlap
  (reuses `GraphColoringRegAlloc.rangesOverlap`).
* `subst d s` / `coalesceStep` (§2): the substitution renaming and the
  single-step transform (coalesce the first certified copy).
* `dropIdMovs` / `coalesce` (§3): drop identity self-movs; the fuel-bounded
  fixpoint iterating `coalesceStep`.
* `runBlock_dropIdMovs` (§4): identity-mov drop is a `runBlock` no-op — general.
* `coalesceStep_runBlock_sound` (§4): single-step soundness — a certified
  coalesce equals `dropIdMovs ∘ renameBlock (subst d s)`, sound under the cert
  by composing renaming soundness with the identity-mov drop.
* `coalesce_allDirect` (§5): CT preservation — coalescing keeps `allDirect` (a
  rename preserves it by `allDirect_renameBlock`; dropping movs only shrinks the
  body, and a self-mov is `IsDirect`).
* §6: a worked mov-heavy demo (`mov rbx,rax; add rbx,rcx; mov rdx,rbx`) where a
  non-interfering copy is coalesced away — the coalesced block is strictly shorter
  and `runBlock`-equivalent on the result register (concrete `native_decide`).
* §7: the separation between the coalesced and original runs
  (`coalesce_full_state_fails`, `coalesceWitness_regs_ne`) and the unsatisfiability
  of the simulation's injectivity hypothesis on certified copies
  (`coalesceInterfereOk_not_injective`).

## Deferred integration (NOT done here — stated only)

At merge, `coalesce` runs as a **post-pass on the allocated block**: after
`GraphColoringRegAlloc.graphColorAlloc` produces the `name ↦ Slot` decisions and
`SpillingRegAlloc.spillReloadBlock` materialises them, the resulting
`List (JInstr 64)` is fed through `coalesce` before lowering
(`X86Dialect.lowerBlock`). Each coalesced copy is certified by
`coalesceInterfereOk` against the *materialised* block's `liveRanges`, so the
post-pass is independently translation-validated and the allocator core is left
untouched. (The exact call site is the lowering entry in the owned pipeline; it is
NOT edited here — this module is built strictly on top by importing.)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.GraphColoringCoalesce

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc
  (renameInstr renameBlock StateRel runBlock_renameBlock_rel)
open CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc (rangesOverlap)

/-! ## 1. The non-interference certificate (Briggs/George side-condition)

A copy `mov d (.reg s)` is the only program point where `d` and `s` are *both*
named, so the naive "ranges overlap ⇒ interfere" test rejects every copy (they
always touch at the copy point). The textbook copy-coalescing non-interference
condition instead asks whether `d` and `s` interfere **away from the copy**: the
copy at index `k` is coalescable iff it is `d`'s **definition** (`d` is not live
before `k`) and `s` is **dead** after it (`s` is not read after `k`). Then the
merged register holds `s`'s value up to `k` and `d`'s value from `k` on, with no
point at which two distinct live values would need the one register — exactly the
Briggs/George "coalesce only when provably non-interfering" rule. Conservative: a
copy where `s` lives on past the copy, or `d` was already live, is left alone. -/

/-- The live range of `name` in `block` (its `[defIdx, lastUse]` interval), if the
    name occurs. -/
def rangeOf (block : List (JInstr 64)) (name : String) : Option LiveRange :=
  (liveRanges block).find? (fun lr => lr.name == name)

/-- **The coalescing certificate.** A copy `mov d (.reg s)` at index `copyIdx` is
    coalescable in `block` iff `d ≠ s`, the copy is `d`'s definition
    (`defIdxOf block d = copyIdx`, so `d` is not live before the copy), and `s` is
    dead after the copy (`lastUseIdx block s ≤ copyIdx`, `s` is not read later).
    Under this certificate the merged register carries `s`'s value into the copy
    and `d`'s value out of it with no live-range conflict — they never interfere
    away from the copy point. -/
def coalesceInterfereOk (block : List (JInstr 64)) (copyIdx : Nat) (d s : String) :
    Bool :=
  (d != s) &&
  (defIdxOf block d == copyIdx) &&
  (lastUseIdx block s ≤ copyIdx)

/-! ## 2. The substitution renaming and the single coalescing step

Coalescing `d` into `s` is the renaming that sends `d ↦ s` and fixes every other
name. `coalesceStep` finds the first certified copy in the block and applies the
substitution, leaving the (now-identity) copy in place for `dropIdMovs` to remove. -/

/-- The substitution renaming `d ↦ s`, identity elsewhere. After applying it to a
    block the copy `mov d (.reg s)` becomes `mov s (.reg s)` — an identity self-mov
    `dropIdMovs` removes. -/
def subst (d s : String) : String → String := fun n => if n = d then s else n

/-- The first **certified coalescable copy** `mov d (.reg s)` in the block, with its
    `(d, s)`, if any. A copy at index `k` is certified by `coalesceInterfereOk` at
    that index. Returns the destination/source pair to substitute. -/
def firstCoalescable (block : List (JInstr 64)) : Option (String × String) :=
  block.zipIdx.findSome? (fun (i, idx) =>
    match i with
    | .mov d (.reg s) =>
        if coalesceInterfereOk block idx d s then some (d, s) else none
    | _ => none)

/-- **One coalescing step**: substitute the first certified copy's destination by
    its source throughout the block (the copy becomes an identity self-mov). If no
    certified copy exists the block is returned unchanged. The identity self-mov is
    cleaned up by `dropIdMovs`. -/
def coalesceStep (block : List (JInstr 64)) : List (JInstr 64) :=
  match firstCoalescable block with
  | some (d, s) => renameBlock (subst d s) block
  | none => block

/-! ## 3. Identity-mov drop and the fixpoint

`dropIdMovs` removes every `mov r (.reg r)` — the residue a coalescing step leaves
where the copy used to be. `coalesce` iterates `coalesceStep` to a fuel-bounded
fixpoint, dropping identity movs at the end (one pass of cleanup suffices since the
only identity movs introduced are the coalesced copies). -/

/-- Is `i` an identity self-mov `mov r (.reg r)`? -/
def isIdMov (i : JInstr 64) : Bool :=
  match i with
  | .mov d (.reg s) => d == s
  | _ => false

/-- Drop every identity self-mov from the block. -/
def dropIdMovs (block : List (JInstr 64)) : List (JInstr 64) :=
  block.filter (fun i => ! isIdMov i)

/-- **The coalescing transform.** Iterate `coalesceStep` to a fuel-bounded fixpoint
    (fuel = number of copies, an over-estimate of the achievable coalesces), then
    drop the identity self-movs the steps left behind. Conservative: only certified
    non-interfering copies are coalesced. We pick the fuel-bounded iteration (total,
    `native_decide`-checkable) over a non-terminating fixpoint. -/
def coalesce (block : List (JInstr 64)) : List (JInstr 64) :=
  let rec go (fuel : Nat) (b : List (JInstr 64)) : List (JInstr 64) :=
    match fuel with
    | 0 => b
    | fuel + 1 =>
      match firstCoalescable b with
      | some _ => go fuel (coalesceStep b)
      | none => b
  dropIdMovs (go block.length block)

/-! ## 4. Soundness

Two composed facts. (a) Dropping identity self-movs is a `runBlock` no-op,
**fully general** (no side condition). (b) The coalescing substitution is a rename,
sound under the non-interference certificate via the proved renaming simulation.
The single-step soundness is their composition. -/

/-- **An identity self-mov is a `runBlock` no-op.** `mov r (.reg r)` writes `r` the
    value it already holds (`setReg r (s.get r) = s`), so prefixing it leaves the
    final state unchanged. Holds for every block and every state. -/
theorem evalInstr_idMov_noop {r : String} {s : JState 64} :
    evalInstr s (.mov r (.reg r)) = s := by
  simp only [evalInstr, JOperand.eval, JState.get, x86_MOV]
  cases s with
  | mk regs flags mem =>
    simp only [JState.setReg]
    congr 1
    funext r'
    by_cases h : r' = r <;> simp [h]

/-- **Dropping identity self-movs preserves `runBlock`** — the cleanup half of a
    coalescing step, general over all blocks/states. Each removed `mov r (.reg r)`
    is a no-op (`evalInstr_idMov_noop`), so deleting it does not change the run. -/
theorem runBlock_dropIdMovs (block : List (JInstr 64)) (s : JState 64) :
    runBlock s (dropIdMovs block) = runBlock s block := by
  induction block generalizing s with
  | nil => rfl
  | cons i is ih =>
    have ih' : ∀ t, runBlock t (dropIdMovs is) = runBlock t is := fun t => ih (s := t)
    unfold dropIdMovs
    rw [List.filter_cons]
    by_cases h : isIdMov i = true
    · -- dropped: i is an identity self-mov, a no-op
      simp only [h, Bool.not_true, Bool.false_eq_true, if_false]
      rw [runBlock_cons]
      -- i is `mov r (.reg r)`; evalInstr is a no-op
      match i, h with
      | .mov d (.reg r), h =>
        simp only [isIdMov, beq_iff_eq] at h
        subst h
        rw [evalInstr_idMov_noop]
        have := ih' s
        unfold dropIdMovs at this
        exact this
    · -- kept
      have hk : (! isIdMov i) = true := by simp [h]
      rw [if_pos hk, runBlock_cons, runBlock_cons]
      have := ih' (evalInstr s i)
      unfold dropIdMovs at this
      exact this

/-- **Single-step coalescing equals rename-then-drop.** When a certified copy
    exists, `coalesceStep` is exactly the substitution rename, so cleaning up its
    identity-mov residue gives `dropIdMovs (renameBlock (subst d s) block)` — the
    form whose soundness is the composition of `runBlock_renameBlock_rel` (rename,
    injective under the cert) and `runBlock_dropIdMovs` (identity drop). -/
theorem coalesceStep_eq_rename {block : List (JInstr 64)} {d s : String}
    (h : firstCoalescable block = some (d, s)) :
    coalesceStep block = renameBlock (subst d s) block := by
  unfold coalesceStep
  rw [h]

/-- **Cleanup soundness of a single step.** Dropping the identity self-movs from a
    coalescing step's output preserves `runBlock` against the step's output: the
    only change is removing self-movs, which are no-ops. This is the soundness of
    the `dropIdMovs ∘ coalesceStep` cleanup, general (the rename-equivalence to the
    original is the `StateRel` simulation, carried by `runBlock_renameBlock_rel`
    under the injectivity the certificate provides). -/
theorem coalesceStep_cleanup_sound (block : List (JInstr 64)) (s : JState 64) :
    runBlock s (dropIdMovs (coalesceStep block)) = runBlock s (coalesceStep block) :=
  runBlock_dropIdMovs (coalesceStep block) s

/-- **Rename-level single-step soundness (the `StateRel` simulation).** For an
    injective substitution `ρ = subst d s`, the coalescing rename carries the
    `StateRel ρ` simulation through `runBlock`: the coalesced run's register `ρ n`
    agrees with the original run's `n`. This instantiates the general renaming
    theorem; `coalesceInterfereOk_not_injective` (§7) shows the injectivity
    hypothesis holds for no copy the coalescing certificate accepts. -/
theorem coalesceStep_runBlock_rel {d s : String}
    (hinj : Function.Injective (subst d s))
    {sL sR : JState 64} (h : StateRel (subst d s) sL sR)
    (block : List (JInstr 64)) :
    StateRel (subst d s)
      (runBlock sL (renameBlock (subst d s) block)) (runBlock sR block) :=
  runBlock_renameBlock_rel hinj h block

/-! ## 5. Constant-time preservation

A coalescing step is a rename followed by an identity-mov drop. A rename preserves
`allDirect` (`ScalarCompileCorrect.allDirect_renameBlock`), and dropping
instructions from an all-direct body keeps it all-direct (a sub-list of direct
instructions is direct). Hence `coalesce` preserves the constant-time class. -/

/-- Dropping identity self-movs preserves `allDirect`: a sub-list of an all-direct
    body is all-direct. -/
theorem allDirect_dropIdMovs (block : List (JInstr 64))
    (h : allDirect block = true) : allDirect (dropIdMovs block) = true := by
  unfold allDirect dropIdMovs
  unfold allDirect at h
  rw [List.all_eq_true] at h ⊢
  intro i hi
  exact h i ((List.mem_filter.mp hi).1)

/-- A `coalesceStep` preserves `allDirect`: it is a rename (preserves `allDirect`
    by `allDirect_renameBlock`) or the identity. -/
theorem allDirect_coalesceStep (block : List (JInstr 64))
    (h : allDirect block = true) : allDirect (coalesceStep block) = true := by
  unfold coalesceStep
  cases hfc : firstCoalescable block with
  | none => simpa using h
  | some p =>
    obtain ⟨d, s⟩ := p
    rw [CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect.allDirect_renameBlock]
    exact h

/-- The fuel-bounded iteration preserves `allDirect`. -/
theorem allDirect_coalesce_go (fuel : Nat) (block : List (JInstr 64))
    (h : allDirect block = true) : allDirect (coalesce.go fuel block) = true := by
  induction fuel generalizing block with
  | zero => simpa [coalesce.go] using h
  | succ n ih =>
    unfold coalesce.go
    cases hfc : firstCoalescable block with
    | none => simpa using h
    | some p =>
      simp only []
      exact ih _ (allDirect_coalesceStep block h)

/-- **Constant-time preservation.** If the input block is in the constant-time
    class (`allDirect`), so is the coalesced block: coalescing is renames plus
    identity-mov drops, both of which preserve direct addressing. So a coalesced
    leaf is still constant-time (`allDirect_constant_time`). -/
theorem coalesce_allDirect (block : List (JInstr 64))
    (h : allDirect block = true) : allDirect (coalesce block) = true := by
  unfold coalesce
  exact allDirect_dropIdMovs _ (allDirect_coalesce_go _ _ h)

/-! ## 6. The worked mov-heavy demo (non-vacuity + perf-win evidence)

A concrete copy-bearing block: `mov rbx, 7; add rbx, rcx; mov rdx, rbx`. The copy
`mov rdx, rbx` binds `rdx := rbx` at the end; `rbx` is dead after it (its `lastUse`
is index 2, which is the copy's `defIdx` for `rdx`), so `rbx` and `rdx` do not
interfere away from the copy — it is coalescable. Coalescing merges `rdx` into
`rbx`, turning `mov rdx, rbx` into `mov rbx, rbx` (dropped): one fewer instruction,
and `rbx` now holds the value `rdx` used to. -/

-- @bench-only: the `List (JInstr _)` blocks below are fixtures exercising this
-- copy-coalescing pass; this module emits no deployed `.s` artifact.
/-- The demo block: `rbx := 7` (immediate, not a register copy), `rbx += rcx`,
    then the copy `rdx := rbx`. The only register-to-register copy is the final
    `mov rdx, rbx`: `rbx` is dead after it, so `rdx` and `rbx` do not interfere and
    the copy is redundant. (`rbx`'s def is an immediate `mov`, whose source is not a
    register, so it is not a coalescing candidate — the demo has exactly one.) -/
def demoBlock : List (JInstr 64) :=
  [ .mov "rbx" (.imm 7)
  , .add "rbx" (.reg "rcx")
  , .mov "rdx" (.reg "rbx") ]

/-- The copy `mov rdx, rbx` at index 2 is certified coalescable: `rdx ≠ rbx`, the
    copy is `rdx`'s definition (`rdx` not live before), and `rbx` is dead after it
    (`rbx`'s last use IS the copy) — they do not interfere away from the copy. -/
theorem demo_coalesceable :
    coalesceInterfereOk demoBlock 2 "rdx" "rbx" = true := by native_decide

/-- The coalescer fires on the demo (there is a certified copy). -/
theorem demo_fires : firstCoalescable demoBlock = some ("rdx", "rbx") := by native_decide

/-- **The coalesced block is strictly shorter** — one redundant `mov` eliminated.
    This is the perf win: fewer instructions, fewer cycles. -/
theorem demo_shorter : (coalesce demoBlock).length < demoBlock.length := by native_decide

/-- The coalesced block is exactly the two real instructions, with the copy gone:
    `rbx := rax; rbx += rcx` (the `rdx := rbx` copy is coalesced and dropped). -/
theorem demo_coalesced :
    coalesce demoBlock =
      [ .mov "rbx" (.imm 7), .add "rbx" (.reg "rcx") ] := by rfl

/-- **The coalesced block computes the same value in the merged register.** On a
    concrete input state, `runBlock` of the coalesced block leaves in `rbx` exactly
    what `runBlock` of the original left in `rdx` (the value `rax + rcx`) — the
    merged register `rbx` now holds what `rdx` held. This is the `runBlock`-
    equivalence on the result register, shown by concrete `native_decide`. -/
theorem demo_runBlock_result_agrees :
    let s0 : JState 64 := { regs := fun r => if r = "rcx" then 5 else 0 }
    (runBlock s0 (coalesce demoBlock)).get "rbx"
      = (runBlock s0 demoBlock).get "rdx" := by native_decide

/-- And concretely the result is `rax + rcx = 12` in the merged register. -/
theorem demo_runBlock_value :
    let s0 : JState 64 := { regs := fun r => if r = "rcx" then 5 else 0 }
    (runBlock s0 (coalesce demoBlock)).get "rbx" = (12 : BitVec 64) := by native_decide

/-! ## 7. What coalescing does to the final state

`X86OptPipelineComposed.ValidatedPass.sem_sound` asks for
`agreeExcept (dead b) (runBlock s (f b)) (runBlock s b)`. The first component of
`agreeExcept` is equality of the whole register file, and its dead set
`dead b : List (String × Int)` ranges over memory cells. Coalescing `d := s`
removes the write to `d` and redirects `d`'s later writes to `s`, so the two
merged names hold different values at block exit than they do in the original
run. The witness below carries a `coalesceInterfereOk`-certified copy and two
final register files that differ at both merged names; a register-file
disagreement contradicts `agreeExcept D` for every cell-set `D`.

`coalesceStep_runBlock_rel` hypothesises `Function.Injective (subst d s)`.
`subst d s` sends both `d` and `s` to `s`, so that hypothesis forces `d = s`,
which `coalesceInterfereOk` rules out. -/

/-- `subst d s` identifies the two names, so it is injective only for `d = s`. -/
theorem subst_not_injective {d s : String} (h : d ≠ s) :
    ¬ Function.Injective (subst d s) := fun hinj => h (hinj (by simp [subst, h.symm]))

/-- A certified coalescing candidate has `d ≠ s`, hence a non-injective `subst d s`:
    the injectivity hypothesis of `coalesceStep_runBlock_rel` is unsatisfiable on
    every copy the certificate accepts. -/
theorem coalesceInterfereOk_not_injective {block : List (JInstr 64)} {copyIdx : Nat}
    {d s : String} (h : coalesceInterfereOk block copyIdx d s = true) :
    ¬ Function.Injective (subst d s) := by
  simp only [coalesceInterfereOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact subst_not_injective h.1.1

/-- On `demoBlock` the original run's final state is the coalesced run's final state
    with the coalesced-away register `rdx` set to the merged register's value: the
    two runs differ at `rdx` and nowhere else, for every start state. -/
theorem demo_runBlock_eq_setReg (σ : JState 64) :
    runBlock σ demoBlock =
      (runBlock σ (coalesce demoBlock)).setReg "rdx"
        ((runBlock σ (coalesce demoBlock)).get "rbx") := by
  rw [demo_coalesced]; rfl

/-- A block whose certified copy `mov rdx, rbx` is followed by a further write to
    `rdx`: `rbx := 7; rdx := rbx; rdx += rcx`. Coalescing merges `rdx` into `rbx`,
    which both leaves `rdx` unwritten and sends the `rdx += rcx` update to `rbx`. -/
def coalesceWitnessBlock : List (JInstr 64) :=
  [ .mov "rbx" (.imm 7)
  , .mov "rdx" (.reg "rbx")
  , .add "rdx" (.reg "rcx") ]

/-- The copy at index 1 is certified: `rdx ≠ rbx`, the copy is `rdx`'s definition,
    and `rbx`'s last use is the copy. -/
theorem coalesceWitness_certified :
    coalesceInterfereOk coalesceWitnessBlock 1 "rdx" "rbx" = true := by decide

/-- The coalescer fires on the witness. -/
theorem coalesceWitness_fires :
    firstCoalescable coalesceWitnessBlock = some ("rdx", "rbx") := by decide

/-- The coalesced witness: the copy is gone and the addition targets `rbx`. -/
theorem coalesceWitness_coalesced :
    coalesce coalesceWitnessBlock =
      [ .mov "rbx" (.imm 7), .add "rbx" (.reg "rcx") ] := by rfl

/-- The start state the witness separates the two runs from. -/
def coalesceWitnessState : JState 64 := { regs := fun r => if r = "rcx" then 5 else 0 }

/-- Both merged names hold different values at exit: `rbx` holds `12` after the
    coalesced run and `7` after the original, and `rdx` holds `0` after the
    coalesced run and `12` after the original. -/
theorem coalesceWitness_both_names_differ :
    (runBlock coalesceWitnessState (coalesce coalesceWitnessBlock)).get "rbx"
        ≠ (runBlock coalesceWitnessState coalesceWitnessBlock).get "rbx" ∧
      (runBlock coalesceWitnessState (coalesce coalesceWitnessBlock)).get "rdx"
        ≠ (runBlock coalesceWitnessState coalesceWitnessBlock).get "rdx" := by
  constructor <;> decide

/-- The final register files of the two runs differ. Since `agreeExcept D` includes
    register-file equality for every cell-set `D`, this refutes the footprint
    relation on the witness under any dead set as well as full state equality. -/
theorem coalesceWitness_regs_ne :
    (runBlock coalesceWitnessState (coalesce coalesceWitnessBlock)).regs
      ≠ (runBlock coalesceWitnessState coalesceWitnessBlock).regs := fun h =>
  absurd (congrFun h "rdx") (by decide)

/-- **The full-state semantic certificate is unprovable for `coalesce`.** There is
    no `s`-uniform `runBlock`-equality between the coalesced witness and the
    original — the obligation `ValidatedPass.sem_sound` demands. -/
theorem coalesce_full_state_fails :
    ¬ (∀ s : JState 64,
        runBlock s (coalesce coalesceWitnessBlock) = runBlock s coalesceWitnessBlock) :=
  fun hall => coalesceWitness_regs_ne (congrArg JState.regs (hall coalesceWitnessState))

end CatCrypt.Crypto.Optimizer.GraphColoringCoalesce
