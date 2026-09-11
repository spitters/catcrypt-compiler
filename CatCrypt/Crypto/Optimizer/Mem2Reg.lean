/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public import CatCrypt.Crypto.Optimizer.StoreToLoadForward

/-!
# Verified mem2reg / scalar-replacement: promote frame-slot scratch to registers (#415)

`StoreToLoadForward.lean` (#412) recovers register *residence* on the frame-resident
X25519 ladder body (#411): a frame cell stored from a register and then reloaded
becomes a register move (`loadMem d fp off → mov d (.reg r)`), so the value stays in a
register over that hop. But forwarding **keeps every instruction**: the rewritten
load is still an instruction (now a `mov`), and — crucially — the *store* that filled
the cell is still there. #413 measured that the residual on the fused body is the
**round-trip instructions themselves**: 96 `loadMem` + 68 `storeMem` per ladder step,
not register pressure (peak GP pressure is only 14, fitting the pool by construction
because every inlined op round-trips its operands through the frame).

The connective pass that *removes* the round-trip is **mem2reg / scalar replacement**:
when a frame slot `(fp, off)` is used as SSA-like scratch — written by a `storeMem` and
read by later `loadMem`s, with no aliasing and no intervening write to that slot, and
the slot is **not** a frame-live output the surrounding code observes — the slot is a
register in disguise. mem2reg

* forwards every `loadMem fp off` of such a slot to a register move (the
  `StoreToLoadForward` rewrite, reused verbatim), and then
* **drops** the `storeMem fp off` that filled it, because after forwarding no later
  instruction reads that cell and the cell is not a live output: the store is dead.

Once the slot's value lives only in a register, the working set exceeds the
pool, and the #413 spilling allocator becomes the right tool to place it — the
`inline → mem2reg → spillRA` pipeline.

## What is proved (sorry-free)

The pass is the composition `forward` (StoreToLoadForward, denotation-preserving on
**all** cells and registers, `storeToLoadForward_runBlock`) followed by **dead-store
elimination** `dse`, whose translation-validation theorem `dse_runBlock_protected` is
the new core:

> dropping a `storeMem fp off _` whose cell `(fp, off)` is never read by the rest of
> the block leaves the `runBlock` final state **unchanged on every register and on
> every cell except possibly `(fp, off)`** — and `(fp, off)` is dead (no later read),
> so the change is unobservable. In particular it agrees on every cell in a *protected*
> set disjoint from the dropped cell (the harness-live ladder outputs).

The store-then-store / store-then-no-read fact is the dual of `StoreToLoadForward`'s
`HeldValid`: a store to a cell with no later read is semantics-transparent on the
observable footprint. We prove it generally (`dseAux` over the whole block, carrying
the "no later read of a dropped cell" side condition as a `NoReadAfter` predicate that
the pass computes), and the mem2reg composition `mem2reg_runBlock_agree` states the
final-state agreement on registers + protected cells. The applied X25519 body's value
identity is the runtime KAT vs RFC 7748 + s2n (the leaf discipline), and the
per-slot scratch promotion count is reported by `mem2reg` on the fused body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Mem2Reg

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (srcNames)
open CatCrypt.Crypto.Optimizer.StoreToLoadForward

/-! ## 1. Cells read by an instruction

mem2reg's safety analysis needs the *memory cells* an instruction reads (the duals of
`writtenRegs`). A `loadMem d base off` reads cell `(base, off)`; a `mulxMem` reads
`(base, off)`; everything else reads no memory cell (registers/immediates only). A
`storeMem base off _` *writes* the cell `(base, off)` (kills any pending read-forward),
and reads none. -/

/-- The memory cell an instruction **reads** (if any). Only `loadMem`/`mulxMem` read
    memory in the emitted subset. -/
def readCell : JInstr 64 → Option (String × Int)
  | .loadMem _ base off => some (base, off)
  | .mulxMem _ _ _ base off => some (base, off)
  -- `lea` computes `base + idx·scale + off` into a register without dereferencing
  -- it, so it reads no cell.
  | .lea _ _ _ _ _ => none
  | _ => none

/-- The memory cell an instruction **writes** (if any). Only `storeMem` writes. -/
def writeCell : JInstr 64 → Option (String × Int)
  | .storeMem base off _ => some (base, off)
  | _ => none

/-- Does an instruction read memory at a **dynamic** (index-register-computed) address?
    A `loadMemIdx`/`storeMemIdx` addresses `[base + idx·scale]`, whose effective offset is
    only known at run time, so it may alias *any* cell of `base`. The static `readCell`
    analysis (which returns `none` for these) cannot exclude the dropped cell, so DSE must
    treat such an instruction as reading (i.e. keeping live) every store before it. -/
def readsDynamic : JInstr 64 → Bool
  | .loadMemIdx _ _ _ _  => true
  | .storeMemIdx _ _ _ _ => true
  -- `loadSym dst sym` re-aliases base `dst`'s bank onto the `.rodata` table `sym`,
  -- so a later access through `dst` reads from `sym` — an effect the static
  -- `readCell` analysis cannot localise. Treat it as a dynamic read (like the SIB
  -- indexed ops): conservatively blocks DSE across it, keeping the elimination sound.
  | .loadSym _ _ => true
  -- `lea` performs no memory access at all, so it is not a dynamic reader even
  -- though its operands look like an address.
  | .lea _ _ _ _ _ => false
  | _ => false

/-- Does the block ever read cell `(base, off)`? (used to decide a store is dead).

    Conservative in the presence of SIB indexed addressing: a `loadMemIdx`/`storeMemIdx`
    (`readsDynamic`) computes its effective offset from an index register and so may alias
    `(base, off)`. We therefore report `true` whenever the block contains such a dynamic
    read, blocking DSE across it — the sound treatment that keeps `dse_runBlock_protected`
    valid even when indexed ops appear (the scalar kernels mem2reg targets contain none, so
    this is the identity there). -/
def cellReadIn (base : String) (off : Int) (block : List (JInstr 64)) : Bool :=
  block.any (fun i => readCell i == some (base, off) || readsDynamic i)

/-- Does the block ever write cell `(base, off)` after the current point? (a later
    store to the same cell also keeps an earlier store live only if a read sits between
    — but for *dead*-store elimination we only drop a store with NO later read, so a
    later overwrite is irrelevant: the value is overwritten before any read). -/
def cellWriteIn (base : String) (off : Int) (block : List (JInstr 64)) : Bool :=
  block.any (fun i => writeCell i == some (base, off))

/-! ## 2. Dead-store elimination

`dse protected block` scans the block; at a `storeMem base off _` it drops the
instruction when (a) the cell `(base, off)` is **not** in `protected` (the
harness-observable output slots) and (b) the *rest* of the block never reads cell
`(base, off)` (`cellReadIn` over the tail is `false`). Every other instruction is kept.
After mem2reg's forwarding sub-pass every reload of a promotable scratch slot has been
turned into a register move, leaving the tail with no read of the cell, and the
matching store is dropped here.

`protected` is a membership test on a cell list; the X25519 application passes the four
ladder-output slots (x2, z2, x3, z3) so their stores are never dropped. -/

/-- Is `(base, off)` a protected (harness-observable) output cell? -/
def isProtected (prot : List (String × Int)) (base : String) (off : Int) : Bool :=
  prot.contains (base, off)

/-- One dead-store-elimination step over a block (tail-recursive scan): keep `i`,
    unless it is a `storeMem` to an unprotected cell never read by the rest. -/
def dseAux (prot : List (String × Int)) : List (JInstr 64) → List (JInstr 64)
  | [] => []
  | i :: is =>
    match i with
    | .storeMem base off _ =>
      if ¬ isProtected prot base off ∧ ¬ cellReadIn base off is then
        dseAux prot is
      else
        i :: dseAux prot is
    | _ => i :: dseAux prot is

/-- **Dead-store elimination.** -/
def dse (prot : List (String × Int)) (block : List (JInstr 64)) : List (JInstr 64) :=
  dseAux prot block

@[simp] theorem dseAux_nil (prot : List (String × Int)) : dseAux prot [] = [] := rfl

/-! ## 3. The mem2reg pass: forward, then drop the now-dead stores

`mem2reg prot block = dse prot (storeToLoadForward block)`. The forwarding sub-pass
turns each reload of a promotable scratch slot into a register move; the DSE sub-pass
then removes the store that filled it (now dead). Protected slots (`prot`) are never
DSE'd, so their stores survive and the harness sees the ladder outputs. -/

/-- **The mem2reg / scalar-replacement pass (forwarding + DSE form).** Fully general,
    fully proved (`mem2reg_runBlock_agree`): forward scratch reloads to register moves, then
    drop the now-dead scratch stores. This is the conservative, denotation-preserving
    promotion — it removes a frame op only where `StoreToLoadForward` already made the cell
    dead. The stronger `promoteSlots` below promotes a designated SSA-scratch cell *fully*
    to a register (both its store and every load become register moves), removing the whole
    round-trip; its core single-cell promotion lemma is proved and the applied body is
    KAT-gated. -/
def mem2reg (prot : List (String × Int)) (block : List (JInstr 64)) : List (JInstr 64) :=
  dse prot (storeToLoadForward block)

/-! ### Full scalar replacement: promote a designated SSA-scratch cell to a register

`promoteCell (b, off) ρ` rewrites, for the single cell `(b, off)` promoted to the fresh
register name `ρ`:

* `storeMem b off (.reg r)` → `mov ρ (.reg r)` (the value enters the promoted register);
* `loadMem d b off`        → `mov d (.reg ρ)` (each use reads the promoted register);

every other instruction is unchanged. When `(b, off)` is **SSA scratch** — written by a
single `storeMem` before any read, never aliased, never a `mulxMem` base — and `ρ` is a
fresh register the program never otherwise names, the promoted block computes the same
register/protected-cell footprint with the cell's entire frame round-trip eliminated. The
applied X25519 body's value identity is the runtime KAT. -/

/-- Promote cell `(b, off)` to register `ρ` in one instruction. -/
def promoteCellInstr (b : String) (off : Int) (ρ : String) : JInstr 64 → JInstr 64
  | .storeMem b' off' (.reg r) =>
      if b' = b ∧ off' = off then .mov ρ (.reg r) else .storeMem b' off' (.reg r)
  | .loadMem d b' off' =>
      if b' = b ∧ off' = off then .mov d (.reg ρ) else .loadMem d b' off'
  | i => i

/-- Promote cell `(b, off)` to register `ρ` over a whole block. -/
def promoteCell (b : String) (off : Int) (ρ : String) (block : List (JInstr 64)) :
    List (JInstr 64) :=
  block.map (promoteCellInstr b off ρ)

/-- A fresh register name for the cell at `(base = "fp", off)`: a tag the leaves never use
    (they name `d0..`, `lo`, `hi`, tagged scratch — never a `%`-prefixed promotion name). -/
def slotReg (off : Int) : String := "%%slot_" ++ toString off

/-- Promote a list of frame offsets (all at base `"fp"`) to fresh registers, folding
    `promoteCell` over the list. Each offset `o` becomes register `slotReg o`. -/
def promoteSlots (offs : List Int) (block : List (JInstr 64)) : List (JInstr 64) :=
  offs.foldl (fun blk o => promoteCell "fp" o (slotReg o) blk) block

/-! ### The single-cell promotion core lemma (the `spillReload_sandwich` analogue)

The heart of scalar replacement: promoting cell `(b, off)` to a register `ρ` turns the
store `storeMem b off (.reg r)` into `mov ρ r` and each load `loadMem d b off` into
`mov d ρ`. The value identity is the **store/use roundtrip = register copy** fact: after
`mov ρ r`, the register `ρ` holds `r`'s value, exactly as the cell `(b, off)` would; a
later `mov d ρ` then writes `d` the same value the `loadMem` would have read — *provided*
the cell `(b, off)` still holds `s.get ρ` at the load (the SSA-scratch invariant: nothing
overwrites the cell or `ρ` between the def and the use).

We prove the canonical building block: a promoted store followed (after a `mid` that
preserves the cell↦ρ binding) by a promoted load denotes the same `runBlock` as the
unpromoted store/load — on the observable footprint that does NOT include `ρ` (a fresh
register) nor the promoted cell (an unprotected scratch slot). This is the `runBlock`
companion to `StoreToLoadForward.storeToLoadForward_runBlock` and
`SpillingRegAlloc.spillReload_sandwich_runBlock`, now for *full* promotion (both the store
and the use leave the frame). -/

/-- `PromoteValid b off ρ s`: the promoted register `ρ` holds the cell `(b, off)`'s value
    in `s`. The invariant the promotion threads — the dual of `SpillValid`, with the cell
    and register roles swapped (here `ρ` is the canonical holder). -/
def PromoteValid (b : String) (off : Int) (ρ : String) (s : JState 64) : Prop :=
  s.get ρ = s.load b off

/-- **A promoted store establishes the invariant and matches the original store on the
    cell.** `evalInstr s (mov ρ r)` makes `ρ` hold `r`'s value; the *original*
    `evalInstr s (storeMem b off r)` makes the cell hold `r`'s value. After each, the
    promoted-register value equals the original-cell value — the promotion's defining
    correspondence at the def site. -/
theorem promoteStore_correspondence (b : String) (off : Int) (ρ r : String) (s : JState 64)
    (_hρ : ρ ≠ r) :
    (evalInstr s (.mov ρ (.reg r))).get ρ
      = (evalInstr s (.storeMem b off (.reg r))).load b off := by
  simp [evalInstr, x86_MOV, JOperand.eval, JState.setReg, JState.store, JState.get, JState.load]

/-- **A promoted load reads the promoted register exactly when the cell would have read.**
    Under `PromoteValid b off ρ s` (the register holds the cell value), `mov d ρ` writes `d`
    the same value `loadMem d b off` would — the promotion's defining correspondence at the
    use site. -/
theorem promoteLoad_correspondence (b : String) (off : Int) (ρ d : String) (s : JState 64)
    (hv : PromoteValid b off ρ s) :
    evalInstr s (.mov d (.reg ρ)) = evalInstr s (.loadMem d b off) := by
  unfold PromoteValid at hv
  show s.setReg d (x86_MOV ((JOperand.reg ρ).eval s)) = s.setReg d (x86_MOV (s.load b off))
  simp only [JOperand.eval, JState.get] at hv ⊢
  rw [hv]

/-! ## 4. Metrics: how many frame ops mem2reg removes

`loadCount`/`storeCount` count the surviving `loadMem`/`storeMem`. Forwarding rewrites a
`loadMem` to a `mov` (so `loadCount` drops); DSE drops a `storeMem` (so `storeCount`
drops). The deliverable reports the totals on the fused body. -/

/-- Number of `loadMem` instructions in a block. -/
def loadCount (block : List (JInstr 64)) : Nat :=
  (block.filter (fun i => match i with | .loadMem _ _ _ => true | _ => false)).length

/-- Number of `storeMem` instructions in a block. -/
def storeCount (block : List (JInstr 64)) : Nat :=
  (block.filter (fun i => match i with | .storeMem _ _ _ => true | _ => false)).length

/-! ## 5. Translation validation for dead-store elimination

The core new fact: **a store to a cell that the rest of the block never reads is
unobservable on the protected footprint.** We prove it on `runBlock` by carrying the
fact that the dropped cell is not read after the store, so the final state agrees on
every register and on every cell except the dropped one — and the dropped cell is not
protected.

We package "agree on registers + protected cells" as `AgreeOn`. The store-skip step is
denotation-preserving on `AgreeOn` because:

* a store changes only its own cell and no register (`evalInstr_storeMem_*`);
* the rest of the block never reads the dropped cell, so running the rest from the
  pre-store state vs. the post-store state lands in states that agree on the
  observable footprint (registers + every cell except the dropped one). -/

/-- Two states **agree on** all registers and on every cell in `prot`. This is the
    observable footprint mem2reg preserves: register file + harness-live output cells. -/
def AgreeOn (prot : List (String × Int)) (s t : JState 64) : Prop :=
  (∀ r, s.get r = t.get r) ∧ (∀ c ∈ prot, s.load c.1 c.2 = t.load c.1 c.2)

theorem AgreeOn.rfl' {prot : List (String × Int)} (s : JState 64) : AgreeOn prot s s :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem AgreeOn.trans {prot : List (String × Int)} {s t u : JState 64}
    (h1 : AgreeOn prot s t) (h2 : AgreeOn prot t u) : AgreeOn prot s u :=
  ⟨fun r => (h1.1 r).trans (h2.1 r), fun c hc => (h1.2 c hc).trans (h2.2 c hc)⟩

/-! ### Two states that agree on registers + ALL cells stay agreeing under any step

The strong invariant we actually thread: two states equal on **every register and
every cell** stay equal under `evalInstr` of any instruction. We use this to slide a
single store-skip: skipping a store to a never-read cell `c` produces a state differing
from the original only at `c`; since `c` is never read again, the rest of the block
runs identically modulo `c`, and `c ∉ prot`. -/

/-- Pointwise full-state equality (every register, every cell) is an `evalInstr`
    congruence — if `s` and `t` agree everywhere, so do their successors. (The flags
    also matter for `adc`/`sbb`/`adcx`/`adox`; we carry them too.) We state it as: equal
    `regs`, `flags`, `mem` ⇒ equal successors, which is immediate since `evalInstr` is a
    function of exactly those three components. -/
theorem evalInstr_congr {s t : JState 64} (i : JInstr 64)
    (hr : s.regs = t.regs) (hf : s.flags = t.flags) (hm : s.mem = t.mem) :
    evalInstr s i = evalInstr t i := by
  have hst : s = t := by cases s; cases t; cases hr; cases hf; cases hm; rfl
  rw [hst]

/-- A run of a block from two states that are **fully equal** lands in fully equal
    states (trivial, by the congruence). -/
theorem runBlock_congr {s t : JState 64} (block : List (JInstr 64))
    (hr : s.regs = t.regs) (hf : s.flags = t.flags) (hm : s.mem = t.mem) :
    runBlock s block = runBlock t block := by
  have hst : s = t := by cases s; cases t; cases hr; cases hf; cases hm; rfl
  rw [hst]

/-! ### The single dead-store skip is observable-preserving

If the tail `is` never reads cell `(base, off)`, then running `is` from the pre-store
state `s` and from the post-store state `s.store base off v` lands in states that agree
on every register and on every cell other than `(base, off)`. Since `(base, off)` is the
*only* cell where the two start states differ, and `is` never reads it, the difference
never propagates into any read — it stays confined to `(base, off)`.

We prove the propagation lemma by induction on the tail, maintaining the invariant
`StoreDiff base off s t`: `t` is `s` with cell `(base, off)` possibly changed, i.e. they
agree on registers, flags, and every cell ≠ `(base, off)`. A step that does not read
`(base, off)` preserves this (its operand reads see equal values), and a step that
writes `(base, off)` re-synchronises that cell too. -/

/-- `t` differs from `s` at most at cell `(base, off)`: equal registers, equal flags,
    equal at every other cell. -/
def StoreDiff (base : String) (off : Int) (s t : JState 64) : Prop :=
  s.regs = t.regs ∧ s.flags = t.flags ∧
    ∀ b o, ¬ (b = base ∧ o = off) → s.mem b o = t.mem b o

theorem StoreDiff.store_intro (base : String) (off : Int) (s : JState 64) (v : BitVec 64) :
    StoreDiff base off s (s.store base off v) := by
  refine ⟨rfl, rfl, ?_⟩
  intro b o hbo
  simp only [JState.store]
  rw [if_neg hbo]

/-! ### Per-arm helpers for the register-only writers

The `writeB5W`/`setReg` ALU and cmov arms all preserve `StoreDiff` for the same reason:
they read register/immediate operands (equal in `s`, `t`), possibly a carry flag (equal
by `hf`), write one register and the five flags (or a `setReg`), and touch no memory.
We factor the two shapes (carry-free `writeB5W`, carry-reading `writeB5W`, and `cmov`'s
`setReg`) so the `StoreDiff.step` case split stays linear. -/

/-- The flag-setting ALU writers that do NOT read a carry-in (`add/sub/imul/and/or/xor/
    shl/shr/sar`): they write `dst` and all flags from `x86_F (s.get dst) (src.eval s)`,
    touch no memory. The successors differ at most at `(base, off)`. -/
theorem b5wStep {base : String} {off : Int} {s t : JState 64} (d : String) (src : JOperand)
    (f : BitVec 64 → BitVec 64 → CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.B5W 64)
    (hr : s.regs = t.regs) (_hf : s.flags = t.flags)
    (hm : ∀ b o, ¬ (b = base ∧ o = off) → s.mem b o = t.mem b o) :
    StoreDiff base off (s.writeB5W d (f (s.get d) (src.eval s)))
      (t.writeB5W d (f (t.get d) (src.eval t))) := by
  have hsrc : src.eval s = src.eval t := by cases src <;> simp [JOperand.eval, hr]
  have hd : s.get d = t.get d := by simp only [JState.get]; rw [hr]
  refine ⟨?_, ?_, ?_⟩
  · simp only [JState.writeB5W]; rw [hr, hsrc, hd]
  · simp only [JState.writeB5W]; rw [hsrc, hd]
  · intro b o _; simp only [JState.writeB5W]; exact hm b o ‹_›

/-- The carry-reading flag-setters (`adc`, `sbb`): write `dst` + flags from
    `x86_F (s.get dst) (src.eval s) (s.flagB cf)`. Same shape, plus the carry-in is equal
    by `hf`. -/
theorem b5wStepFlag {base : String} {off : Int} {s t : JState 64} (d : String)
    (src : JOperand)
    (f : BitVec 64 → BitVec 64 → Bool →
          CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.B5W 64)
    (hr : s.regs = t.regs) (hf : s.flags = t.flags)
    (hm : ∀ b o, ¬ (b = base ∧ o = off) → s.mem b o = t.mem b o) :
    StoreDiff base off (s.writeB5W d (f (s.get d) (src.eval s) (s.flagB (·.cf))))
      (t.writeB5W d (f (t.get d) (src.eval t) (t.flagB (·.cf)))) := by
  have hsrc : src.eval s = src.eval t := by cases src <;> simp [JOperand.eval, hr]
  have hd : s.get d = t.get d := by simp only [JState.get]; rw [hr]
  have hcf : s.flagB (·.cf) = t.flagB (·.cf) := by simp only [JState.flagB]; rw [hf]
  refine ⟨?_, ?_, ?_⟩
  · simp only [JState.writeB5W]; rw [hr, hsrc, hd, hcf]
  · simp only [JState.writeB5W]; rw [hsrc, hd, hcf]
  · intro b o _; simp only [JState.writeB5W]; exact hm b o ‹_›

/-- The cmov writers reading flag-projection `pf` (`cmove`/`cmovb`): `setReg dst
    (x86_CMOVcc (pf s) (src.eval s) (s.get dst))`. -/
theorem cmovStep {base : String} {off : Int} {s t : JState 64} (d : String) (src : JOperand)
    (pf : JState 64 → Bool)
    (hpf : pf s = pf t)
    (hr : s.regs = t.regs) (hf : s.flags = t.flags)
    (hm : ∀ b o, ¬ (b = base ∧ o = off) → s.mem b o = t.mem b o) :
    StoreDiff base off (s.setReg d (x86_CMOVcc (pf s) (src.eval s) (s.get d)))
      (t.setReg d (x86_CMOVcc (pf t) (src.eval t) (t.get d))) := by
  have hsrc : src.eval s = src.eval t := by cases src <;> simp [JOperand.eval, hr]
  have hd : s.get d = t.get d := by simp only [JState.get]; rw [hr]
  refine ⟨?_, ?_, ?_⟩
  · simp only [JState.setReg]; rw [hr, hsrc, hd, hpf]
  · simp only [JState.setReg]; exact hf
  · intro b o _; simp only [JState.setReg]; exact hm b o ‹_›

/-- The cmov writer reading the *negation* of `pf` (`cmovne`). -/
theorem cmovStepNot {base : String} {off : Int} {s t : JState 64} (d : String)
    (src : JOperand) (pf : JState 64 → Bool)
    (hpf : pf s = pf t)
    (hr : s.regs = t.regs) (hf : s.flags = t.flags)
    (hm : ∀ b o, ¬ (b = base ∧ o = off) → s.mem b o = t.mem b o) :
    StoreDiff base off (s.setReg d (x86_CMOVcc (! pf s) (src.eval s) (s.get d)))
      (t.setReg d (x86_CMOVcc (! pf t) (src.eval t) (t.get d))) := by
  have hsrc : src.eval s = src.eval t := by cases src <;> simp [JOperand.eval, hr]
  have hd : s.get d = t.get d := by simp only [JState.get]; rw [hr]
  refine ⟨?_, ?_, ?_⟩
  · simp only [JState.setReg]; rw [hr, hsrc, hd, hpf]
  · simp only [JState.setReg]; exact hf
  · intro b o _; simp only [JState.setReg]; exact hm b o ‹_›

/-- The operands an instruction reads evaluate equally in `s` and `t` when `t` differs
    from `s` only at a cell the instruction does not read. The register operands agree
    because `s.regs = t.regs`; the only memory read (`loadMem`/`mulxMem`) is at the
    instruction's `readCell`, which by hypothesis is not `(base, off)`. Therefore
    `evalInstr` produces successors that again differ at most at `(base, off)` — unless
    the instruction itself writes `(base, off)`, in which case they re-sync. -/
theorem StoreDiff.step {base : String} {off : Int} {s t : JState 64}
    (i : JInstr 64) (hd : StoreDiff base off s t)
    (hread : readCell i ≠ some (base, off)) (hdyn : readsDynamic i = false) :
    StoreDiff base off (evalInstr s i) (evalInstr t i) := by
  obtain ⟨hr, hf, hm⟩ := hd
  -- registers and flags are equal in s,t; the only place s,t differ is cell (base,off),
  -- which i does not read.  We case on i.
  cases i with
  | mov d src =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.setReg]; rw [hr]
      have : src.eval s = src.eval t := by cases src <;> simp [JOperand.eval, hr]
      rw [this]
    · simp only [evalInstr, JState.setReg]; exact hf
    · intro b o _; simp only [evalInstr, JState.setReg]; exact hm b o ‹_›
  | loadMem d b' o' =>
    have hne : ¬ (b' = base ∧ o' = off) := by
      intro hc; exact hread (by simp only [readCell]; rw [hc.1, hc.2])
    have hcell : s.load b' o' = t.load b' o' := by simp only [JState.load]; exact hm b' o' hne
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.setReg]
      rw [hr, hcell]
    · simp only [evalInstr, JState.setReg]; exact hf
    · intro b o _; simp only [evalInstr, JState.setReg]; exact hm b o ‹_›
  | mulxMem dh dl a b' o' =>
    have hne : ¬ (b' = base ∧ o' = off) := by
      intro hc; exact hread (by simp only [readCell]; rw [hc.1, hc.2])
    have hcell : s.load b' o' = t.load b' o' := by simp only [JState.load]; exact hm b' o' hne
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.setReg]
      have ha : a.eval s = a.eval t := by cases a <;> simp [JOperand.eval, hr]
      rw [ha, hcell, hr]
    · simp only [evalInstr, JState.setReg]; exact hf
    · intro b o _; simp only [evalInstr, JState.setReg]; exact hm b o ‹_›
  | storeMem b' o' src =>
    -- a store: registers + flags unchanged; the written cell re-syncs to the same value
    -- (operands evaluate equally), other cells are unchanged.
    have hsrc : src.eval s = src.eval t := by cases src <;> simp [JOperand.eval, hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.store]; exact hr
    · simp only [evalInstr, JState.store]; exact hf
    · intro b o hbo
      simp only [evalInstr, JState.store, x86_MOV]
      by_cases hc : b = b' ∧ o = o'
      · rw [if_pos hc, if_pos hc, hsrc]
      · rw [if_neg hc, if_neg hc]; exact hm b o hbo
  | mulx dh dl a b' =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.setReg]
      have ha : a.eval s = a.eval t := by cases a <;> simp [JOperand.eval, hr]
      have hb : b'.eval s = b'.eval t := by cases b' <;> simp [JOperand.eval, hr]
      rw [ha, hb, hr]
    · simp only [evalInstr, JState.setReg]; exact hf
    · intro b o _; simp only [evalInstr, JState.setReg]; exact hm b o ‹_›
  | adcx d src =>
    have hsrc : src.eval s = src.eval t := by cases src <;> simp [JOperand.eval, hr]
    have hd : s.get d = t.get d := by simp only [JState.get]; rw [hr]
    have hcf : s.flagB (·.cf) = t.flagB (·.cf) := by simp only [JState.flagB]; rw [hf]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr]; rw [hsrc, hd, hcf, hr]
    · simp only [evalInstr]; rw [hf, hd, hsrc, hcf]
    · intro b o _; simp only [evalInstr]; exact hm b o ‹_›
  | adox d src =>
    have hsrc : src.eval s = src.eval t := by cases src <;> simp [JOperand.eval, hr]
    have hd : s.get d = t.get d := by simp only [JState.get]; rw [hr]
    have hof : s.flagB (·.of) = t.flagB (·.of) := by simp only [JState.flagB]; rw [hf]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr]; rw [hsrc, hd, hof, hr]
    · simp only [evalInstr]; rw [hf, hd, hsrc, hof]
    · intro b o _; simp only [evalInstr]; exact hm b o ‹_›
  | neg d =>
    have hd : s.get d = t.get d := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.writeB5W]; rw [hr, hd]
    · simp only [evalInstr, JState.writeB5W]; rw [hd]
    · intro b o _; simp only [evalInstr, JState.writeB5W]; exact hm b o ‹_›
  | setc d =>
    -- `setc d := if CF then 1 else 0`: a `setReg` writing only `d`, reading only the
    -- carry flag (equal in s,t by `hf`); touches no memory.
    have hcf : s.flagB (·.cf) = t.flagB (·.cf) := by simp only [JState.flagB]; rw [hf]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.setReg]; rw [hr, hcf]
    · simp only [evalInstr, JState.setReg]; exact hf
    · intro b o _; simp only [evalInstr, JState.setReg]; exact hm b o ‹_›
  | test a src =>
    -- `test` writes the five flags and no register: the register files stay equal
    -- verbatim, the flags are computed from equal reads, and memory is untouched.
    have hsrc : src.eval s = src.eval t := by cases src <;> simp [JOperand.eval, hr]
    have ha : s.get a = t.get a := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.writeB5]; exact hr
    · simp only [evalInstr, JState.writeB5]; rw [ha, hsrc]
    · intro b o _; simp only [evalInstr, JState.writeB5]; exact hm b o ‹_›
  | cmp a src =>
    -- `cmp` is `test`'s shape: five flags from equal reads, no register write.
    have hsrc : src.eval s = src.eval t := by cases src <;> simp [JOperand.eval, hr]
    have ha : s.get a = t.get a := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.writeB5]; exact hr
    · simp only [evalInstr, JState.writeB5]; rw [ha, hsrc]
    · intro x y hxy; simp only [evalInstr, JState.writeB5]; exact hm x y hxy
  | not_ d =>
    have hd : s.get d = t.get d := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.setReg]; rw [hr, hd]
    · simp only [evalInstr, JState.setReg]; exact hf
    · intro x y hxy; simp only [evalInstr, JState.setReg]; exact hm x y hxy
  | andn d a c =>
    have ha : s.get a = t.get a := by simp only [JState.get]; rw [hr]
    have hc : s.get c = t.get c := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.writeB5W]; rw [hr, ha, hc]
    · simp only [evalInstr, JState.writeB5W]; rw [ha, hc]
    · intro x y hxy; simp only [evalInstr, JState.writeB5W]; exact hm x y hxy
  | rol d amt =>
    -- `writeB2W` writes `OF`/`CF` over the pre-state flags, which are equal by `hf`.
    have hsrc : amt.eval s = amt.eval t := by cases amt <;> simp [JOperand.eval, hr]
    have hd : s.get d = t.get d := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.writeB2W]; rw [hr, hd, hsrc]
    · simp only [evalInstr, JState.writeB2W]; rw [hf, hd, hsrc]
    · intro x y hxy; simp only [evalInstr, JState.writeB2W]; exact hm x y hxy
  | ror d amt =>
    have hsrc : amt.eval s = amt.eval t := by cases amt <;> simp [JOperand.eval, hr]
    have hd : s.get d = t.get d := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.writeB2W]; rw [hr, hd, hsrc]
    · simp only [evalInstr, JState.writeB2W]; rw [hf, hd, hsrc]
    · intro x y hxy; simp only [evalInstr, JState.writeB2W]; exact hm x y hxy
  | rorx d src amt =>
    have hsrc : amt.eval s = amt.eval t := by cases amt <;> simp [JOperand.eval, hr]
    have hv : s.get src = t.get src := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.setReg]; rw [hr, hv, hsrc]
    · simp only [evalInstr, JState.setReg]; exact hf
    · intro x y hxy; simp only [evalInstr, JState.setReg]; exact hm x y hxy
  | shlx d src c =>
    have hv : s.get src = t.get src := by simp only [JState.get]; rw [hr]
    have hc : s.get c = t.get c := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.setReg]; rw [hr, hv, hc]
    · simp only [evalInstr, JState.setReg]; exact hf
    · intro x y hxy; simp only [evalInstr, JState.setReg]; exact hm x y hxy
  | shrx d src c =>
    have hv : s.get src = t.get src := by simp only [JState.get]; rw [hr]
    have hc : s.get c = t.get c := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.setReg]; rw [hr, hv, hc]
    · simp only [evalInstr, JState.setReg]; exact hf
    · intro x y hxy; simp only [evalInstr, JState.setReg]; exact hm x y hxy
  | sarx d src c =>
    have hv : s.get src = t.get src := by simp only [JState.get]; rw [hr]
    have hc : s.get c = t.get c := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.setReg]; rw [hr, hv, hc]
    · simp only [evalInstr, JState.setReg]; exact hf
    · intro x y hxy; simp only [evalInstr, JState.setReg]; exact hm x y hxy
  | movzx d sw src =>
    have hv : s.get src = t.get src := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.setReg]; rw [hr, hv]
    · simp only [evalInstr, JState.setReg]; exact hf
    · intro x y hxy; simp only [evalInstr, JState.setReg]; exact hm x y hxy
  | movsx d sw src =>
    have hv : s.get src = t.get src := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.setReg]; rw [hr, hv]
    · simp only [evalInstr, JState.setReg]; exact hf
    · intro x y hxy; simp only [evalInstr, JState.setReg]; exact hm x y hxy
  | lea d bs ix sc dsp =>
    -- an address computation: the two address registers are read, no cell is.
    have hb : s.get bs = t.get bs := by simp only [JState.get]; rw [hr]
    have hi : s.get ix = t.get ix := by simp only [JState.get]; rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalInstr, JState.setReg]; rw [hr, hb, hi]
    · simp only [evalInstr, JState.setReg]; exact hf
    · intro x y hxy; simp only [evalInstr, JState.setReg]; exact hm x y hxy
  | add d src => simpa only [evalInstr] using b5wStep d src x86_ADD hr hf hm
  | sub d src => simpa only [evalInstr] using b5wStep d src x86_SUB hr hf hm
  | adc d src => simpa only [evalInstr] using b5wStepFlag d src x86_ADC hr hf hm
  | sbb d src => simpa only [evalInstr] using b5wStepFlag d src x86_SBB hr hf hm
  | imul d src => simpa only [evalInstr] using b5wStep d src x86_IMULt hr hf hm
  | and_ d src => simpa only [evalInstr] using b5wStep d src x86_AND hr hf hm
  | or_ d src => simpa only [evalInstr] using b5wStep d src x86_OR hr hf hm
  | xor_ d src => simpa only [evalInstr] using b5wStep d src x86_XOR hr hf hm
  | shl d src => simpa only [evalInstr] using b5wStep d src x86_SHL hr hf hm
  | shr d src => simpa only [evalInstr] using b5wStep d src x86_SHR hr hf hm
  | sar d src => simpa only [evalInstr] using b5wStep d src x86_SAR hr hf hm
  | cmove d src =>
      have hpf : s.flagB (·.zf) = t.flagB (·.zf) := by simp only [JState.flagB]; rw [hf]
      simpa only [evalInstr] using cmovStep d src (fun st => st.flagB (·.zf)) hpf hr hf hm
  | cmovne d src =>
      have hpf : s.flagB (·.zf) = t.flagB (·.zf) := by simp only [JState.flagB]; rw [hf]
      simpa only [evalInstr] using cmovStepNot d src (fun st => st.flagB (·.zf)) hpf hr hf hm
  | cmovb d src =>
      have hpf : s.flagB (·.cf) = t.flagB (·.cf) := by simp only [JState.flagB]; rw [hf]
      simpa only [evalInstr] using cmovStep d src (fun st => st.flagB (·.cf)) hpf hr hf hm
  -- The SIB indexed reads/writes have a *dynamic* effective offset that may alias the
  -- dropped cell; `StoreDiff` propagation across them is therefore excluded by the
  -- `readsDynamic i = false` hypothesis (these constructors set it `true`).
  | loadMemIdx d base' idx scale => simp [readsDynamic] at hdyn
  | storeMemIdx base' idx scale src => simp [readsDynamic] at hdyn
  -- `loadSym` re-aliases a memory bank (a dynamic read of the `.rodata` table), so it
  -- is likewise excluded by the `readsDynamic i = false` hypothesis.
  | loadSym d sym => simp [readsDynamic] at hdyn

/-! ### StoreDiff propagates through a block that never reads the dropped cell

If `is` never reads cell `(base, off)` (`cellReadIn base off is = false`), then
`StoreDiff base off s t` is preserved by `runBlock s is` / `runBlock t is`: each step
neither reads the differing cell (so its operand reads see equal values) nor — once we
reach the end — observes it. Hence the two runs land in states that again differ at most
at `(base, off)`. -/

/-- `cellReadIn` over a cons splits into the head's `readCell`/`readsDynamic` and the tail. -/
theorem cellReadIn_cons (base : String) (off : Int) (i : JInstr 64)
    (is : List (JInstr 64)) :
    cellReadIn base off (i :: is) =
      ((readCell i == some (base, off) || readsDynamic i) || cellReadIn base off is) := by
  simp [cellReadIn, List.any_cons]

/-- If the head does not read the dropped cell, then `readCell i ≠ some (base, off)`. -/
theorem readCell_ne_of_not_read {base : String} {off : Int} {i : JInstr 64}
    {is : List (JInstr 64)} (h : cellReadIn base off (i :: is) = false) :
    readCell i ≠ some (base, off) := by
  rw [cellReadIn_cons] at h
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  exact h.1.1

/-- If the head is not read-live, it is also not a dynamic (indexed) read. -/
theorem readsDynamic_false_of_not_read {base : String} {off : Int} {i : JInstr 64}
    {is : List (JInstr 64)} (h : cellReadIn base off (i :: is) = false) :
    readsDynamic i = false := by
  rw [cellReadIn_cons] at h
  simp only [Bool.or_eq_false_iff] at h
  exact h.1.2

/-- The tail's `cellReadIn` is also false. -/
theorem cellReadIn_tail_false {base : String} {off : Int} {i : JInstr 64}
    {is : List (JInstr 64)} (h : cellReadIn base off (i :: is) = false) :
    cellReadIn base off is = false := by
  rw [cellReadIn_cons] at h
  simp only [Bool.or_eq_false_iff] at h
  exact h.2

/-- **StoreDiff propagation.** If `is` never reads `(base, off)`, running it from two
    states differing at most at that cell lands in states still differing at most there. -/
theorem StoreDiff.runBlock {base : String} {off : Int} {s t : JState 64}
    (is : List (JInstr 64)) (hd : StoreDiff base off s t)
    (hnoread : cellReadIn base off is = false) :
    StoreDiff base off (runBlock s is) (runBlock t is) := by
  induction is generalizing s t with
  | nil => simpa using hd
  | cons i is ih =>
    rw [runBlock_cons, runBlock_cons]
    have hstep := hd.step i (readCell_ne_of_not_read hnoread)
      (readsDynamic_false_of_not_read hnoread)
    exact ih hstep (cellReadIn_tail_false hnoread)

/-! ## 6. The dead-store-elimination soundness theorem

The DSE'd block's `runBlock` final state **agrees with** the original's on every register
and every protected cell. The proof is an induction on the block:

* a kept instruction `i`: both sides step by `evalInstr _ i`; the IH gives `AgreeOn` at
  the tail, and `runBlock_congr` is not needed — we re-run the SAME instruction, so
  `AgreeOn` is preserved by `runBlock` of the dropped/kept tail under the matching
  congruence. We package this via `AgreeOn` transitivity using the propagation lemma.
* a dropped store `storeMem base off v`: the original side is
  `runBlock (s.store base off _) is`, the DSE side is `runBlock s (dseAux prot is)`. The
  store-skipped state and `s` differ only at `(base, off)` (`StoreDiff.store_intro`),
  which `is` never reads (the DSE guard `¬cellReadIn base off is`), so by
  `StoreDiff.runBlock` the two original-side runs agree on regs + every cell ≠
  `(base, off)`. Since the dropped cell is not protected (the other DSE guard), they
  agree on every protected cell. The IH closes the DSE side. -/

/-- A `StoreDiff` implies `AgreeOn prot` whenever the differing cell `(base, off)` is not
    in `prot`: registers are equal, and every protected cell ≠ `(base, off)` is equal. -/
theorem StoreDiff.agreeOn {prot : List (String × Int)} {base : String} {off : Int}
    {s t : JState 64} (hd : StoreDiff base off s t)
    (hp : isProtected prot base off = false) : AgreeOn prot s t := by
  obtain ⟨hr, _, hm⟩ := hd
  refine ⟨fun r => by simp only [JState.get]; rw [hr], fun c hc => ?_⟩
  have hcne : ¬ (c.1 = base ∧ c.2 = off) := by
    intro hcon
    have : c = (base, off) := by rw [Prod.ext_iff]; exact hcon
    rw [this] at hc
    simp only [isProtected, List.contains_eq_mem, decide_eq_false_iff_not] at hp
    exact hp hc
  simp only [JState.load]; exact hm c.1 c.2 hcne

/-- A kept instruction preserves `AgreeOn` on the two whole runs, given the tail
    agreement: both sides run the SAME `i`, so the successor states are literally equal,
    and the tail `AgreeOn` carries through. We need only that running the same suffix
    from the same state agrees — which is `rfl`-level once the prefixes match. -/
theorem dseAux_runBlock_agree (prot : List (String × Int)) (block : List (JInstr 64)) :
    ∀ s : JState 64, AgreeOn prot (runBlock s (dseAux prot block)) (runBlock s block) := by
  induction block with
  | nil => intro s; exact AgreeOn.rfl' s
  | cons i is ih =>
    intro s
    cases hi : i with
    | storeMem base off v =>
      simp only [dseAux]
      by_cases hguard : ¬ isProtected prot base off ∧ ¬ cellReadIn base off is
      · -- dropped
        rw [if_pos hguard]
        -- original side: runBlock (evalInstr s (storeMem base off v)) is
        rw [runBlock_cons]
        -- DSE side: runBlock s (dseAux prot is); IH gives it ~ runBlock s is
        -- bridge runBlock s is  ~  runBlock (store ..) is via StoreDiff
        have hstore : evalInstr s (.storeMem base off v) = s.store base off (x86_MOV (v.eval s)) := by
          simp [evalInstr]
        have hp : isProtected prot base off = false := by
          simpa using hguard.1
        have hnoread : cellReadIn base off is = false := by simpa using hguard.2
        have hsd : StoreDiff base off s (s.store base off (x86_MOV (v.eval s))) :=
          StoreDiff.store_intro base off s _
        have hprop := hsd.runBlock is hnoread
        -- AgreeOn (runBlock s (dseAux .. is)) (runBlock s is)  [IH]
        -- AgreeOn (runBlock s is) (runBlock (store..) is)       [hprop.agreeOn]
        refine (ih s).trans ?_
        rw [hstore]
        exact hprop.agreeOn hp
      · -- kept
        rw [if_neg hguard, runBlock_cons, runBlock_cons]
        exact ih (evalInstr s (.storeMem base off v))
    | _ =>
      -- non-store: dseAux keeps it; both sides step by the same evalInstr s i
      simp only [dseAux]
      rw [runBlock_cons, runBlock_cons]
      exact ih (evalInstr s _)

/-- **Dead-store elimination is denotation-preserving on the protected footprint.** For
    every state, the DSE'd block's `runBlock` final state agrees with the original's on
    every register and every protected cell. -/
theorem dse_runBlock_protected (prot : List (String × Int)) (block : List (JInstr 64))
    (s : JState 64) : AgreeOn prot (runBlock s (dse prot block)) (runBlock s block) :=
  dseAux_runBlock_agree prot block s

/-! ## 7. The mem2reg composition: forward, then DSE — protected-footprint preserving

`mem2reg prot block = dse prot (storeToLoadForward block)`. Forwarding is
denotation-preserving on the FULL state (`storeToLoadForward_runBlock`), so it is in
particular `AgreeOn`-preserving; DSE is `AgreeOn`-preserving on the protected footprint.
Composing, `mem2reg`'s output agrees with the original on registers + protected cells —
the in-Lean translation-validation certificate for the scalar-replacement pass. -/

/-- Full-state equality lifts to `AgreeOn` for any `prot`. -/
theorem AgreeOn.of_eq {prot : List (String × Int)} {s t : JState 64} (h : s = t) :
    AgreeOn prot s t := by subst h; exact AgreeOn.rfl' s

/-- **mem2reg translation validation.** For every state, the mem2reg'd block's `runBlock`
    final state agrees with the original's on every register and every protected cell.
    Forwarding preserves the whole state; DSE preserves the protected footprint. No
    `sorry`. -/
theorem mem2reg_runBlock_agree (prot : List (String × Int)) (block : List (JInstr 64))
    (s : JState 64) :
    AgreeOn prot (runBlock s (mem2reg prot block)) (runBlock s block) := by
  unfold mem2reg
  refine (dse_runBlock_protected prot (storeToLoadForward block) s).trans ?_
  exact AgreeOn.of_eq (storeToLoadForward_runBlock block s)

/-- **Dialect-level form.** Through `X86Dialect.lowerBlock_denote_closed`, the lowered
    `Com` of the mem2reg'd block and of the original denote states agreeing on registers +
    protected cells, on every incoming state. -/
theorem mem2reg_lowering_agree (prot : List (String × Int)) (block : List (JInstr 64))
    (s : JState 64) :
    AgreeOn prot
      ((lowerBlock (Γ := []) (mem2reg prot block)).denote (.cons s .nil))
      ((lowerBlock (Γ := []) block).denote (.cons s .nil)) := by
  rw [lowerBlock_denote_closed (mem2reg prot block) s, lowerBlock_denote_closed block s]
  exact mem2reg_runBlock_agree prot block s

/-! ## 8. Whole-body soundness of full scalar replacement `promoteCell` (#417)

§3 proved the single-instruction correspondences (`promoteStore_correspondence`,
`promoteLoad_correspondence`). What #415 left as a KAT assumption — and what #416 caught
as an *unsound* gap — is the **whole-body** identity: `runBlock (promoteCell b off ρ block)`
vs `runBlock block`. The gap is real: the naive `promoteSlots` promoted scratch cells that
are read by a `mulxMem` (the s2n multiplicand-from-memory fold). `promoteCellInstr` rewrites
only `loadMem`/`storeMem`, **never** `mulxMem`, so a promoted store (`storeMem → mov ρ r`)
removes the frame write while the `mulxMem` still reads the now-never-written frame cell —
the promoted body reads stale memory. (Concretely on the X25519 ladder: the slots A, AA, B,
E, C, D, T are each read as a `mulxMem` multiplicand.)

The corrected analysis: a cell `(b, off)` is **promotable** only when it is read solely via
`loadMem` (never `mulxMem`, never as a `mulxMem`/load base from another base alias), written
only by register-source `storeMem`, and `ρ` is a register name the block never otherwise
mentions (fresh). Under these conditions `promoteCell` is denotation-preserving on every
register except `ρ` and every cell except `(b, off)` — and `(b, off)` is unprotected scratch,
`ρ` is not observable. We prove this generally below (no KAT, no `sorry`). -/

/-- Registers an instruction **reads** (operands), in the model's evaluation. (We only
    need: a fresh `ρ` is not among these, so the instruction's reads agree across the
    ρ-difference.) Mirrors `AsmPrinter.jinstrNames` minus the written destination(s). -/
def readRegs : JInstr 64 → List String
  | .mov _ s | .add _ s | .sub _ s | .adc _ s | .sbb _ s | .imul _ s
  | .and_ _ s | .or_ _ s | .xor_ _ s | .shl _ s | .shr _ s | .sar _ s
  | .adcx _ s | .adox _ s => srcNames s
  | .neg d => [d]                       -- neg reads its own dst
  | .test a s => a :: srcNames s        -- both test operands are reads, neither a dst
  | .cmp a s => a :: srcNames s         -- both cmp operands are reads, neither a dst
  | .setc _ => []                       -- setc reads only the CF flag, no GP register
  | .not_ d => [d]                      -- not_ reads its own dst
  | .andn _ a c => [a, c]               -- andn is non-destructive in both sources
  | .rol d s | .ror d s => d :: srcNames s  -- the rotates read their dst and the count
  | .rorx _ src s => src :: srcNames s
  | .shlx _ src c | .shrx _ src c | .sarx _ src c => [src, c]
  | .movzx _ _ src | .movsx _ _ src => [src]
  | .lea _ base idx _ _ => [base, idx]  -- the two address registers, no memory
  | .cmove d s | .cmovne d s | .cmovb d s => d :: srcNames s  -- cmov reads dst (kept value)
  | .mulx _ _ a b => srcNames a ++ srcNames b
  | .mulxMem _ _ a _ _ => srcNames a
  | .loadMem _ _ _ => []
  -- `loadSym dst sym` reads no register (`sym` is a `.rodata` label, not a GP).
  | .loadSym _ _ => []
  | .storeMem _ _ s => srcNames s
  -- SIB indexed addressing reads the base + index registers (and the stored source)
  | .loadMemIdx _ base idx _ => [base, idx]
  | .storeMemIdx base idx _ s => base :: idx :: srcNames s

/-- The cell an instruction reads **other than** via the promoted `loadMem`, plus the
    register read-set, do not touch `ρ` / `(b,off)` — packaged as the promotability side
    conditions for one instruction. `i` is *transparent* to the promotion of `(b,off)→ρ`
    when: it does not name `ρ` (read or written), it does not read `(b,off)` (so neither a
    `loadMem`/`mulxMem` at `(b,off)`), and it does not write `(b,off)` via `storeMem`. The
    promoted store/load instructions are handled separately; this predicate is for the
    *kept* instructions. -/
def InstrTransparent (b : String) (off : Int) (ρ : String) (i : JInstr 64) : Prop :=
  ρ ∉ writtenRegsI i ∧ ρ ∉ readRegs i ∧ readCell i ≠ some (b, off) ∧ writeCell i ≠ some (b, off)
    ∧ readsDynamic i = false
where
  /-- destination register(s) written by `i` (the `setReg`/`writeB5W` targets). -/
  writtenRegsI : JInstr 64 → List String
  | .mov d _ | .add d _ | .sub d _ | .adc d _ | .sbb d _ | .imul d _ | .neg d | .setc d
  | .and_ d _ | .or_ d _ | .xor_ d _ | .shl d _ | .shr d _ | .sar d _
  | .cmove d _ | .cmovne d _ | .cmovb d _ | .adcx d _ | .adox d _
  | .loadMem d _ _ | .loadMemIdx d _ _ _ | .loadSym d _
  | .not_ d | .andn d _ _ | .rol d _ | .ror d _ | .rorx d _ _
  | .shlx d _ _ | .shrx d _ _ | .sarx d _ _
  | .movzx d _ _ | .movsx d _ _ | .lea d _ _ _ _ => [d]
  | .mulx dh dl _ _ | .mulxMem dh dl _ _ _ => [dh, dl]
  | .storeMem _ _ _ | .storeMemIdx _ _ _ _ => []
  -- `test` and `cmp` write the five flags and no register.
  | .test _ _ => []
  | .cmp _ _ => []

open InstrTransparent (writtenRegsI)

/-- The promotion invariant relating the **original** state `s` and the **promoted** state
    `t`: they agree on every register except `ρ`, the promoted register `ρ` (in `t`) holds
    the original cell value (`s.load b off`), flags agree, and memory agrees on every cell
    except possibly the promoted cell `(b, off)`. -/
def PromoteRel (b : String) (off : Int) (ρ : String) (s t : JState 64) : Prop :=
  (∀ r, r ≠ ρ → s.get r = t.get r) ∧
  t.get ρ = s.load b off ∧
  s.flags = t.flags ∧
  (∀ b' o', ¬ (b' = b ∧ o' = off) → s.mem b' o' = t.mem b' o')

theorem PromoteRel.reg_read {b : String} {off : Int} {ρ : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) (src : JOperand) (hρ : ρ ∉ srcNames src) :
    src.eval s = src.eval t := by
  cases src with
  | imm v => simp [JOperand.eval]
  | reg r =>
    have hne : r ≠ ρ := by intro hc; subst hc; exact hρ (by simp [srcNames])
    simp only [JOperand.eval]
    exact h.1 r hne

/-- Reading a register `r ≠ ρ` agrees across `PromoteRel`. -/
theorem PromoteRel.get {b : String} {off : Int} {ρ : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) {r : String} (hr : r ≠ ρ) : s.get r = t.get r :=
  h.1 r hr

/-- Reading any flag agrees across `PromoteRel` (flags are equal). -/
theorem PromoteRel.flagB {b : String} {off : Int} {ρ : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) (f : RFlags → JFlag) : s.flagB f = t.flagB f := by
  simp only [JState.flagB]; rw [h.2.2.1]

/-- Reading a cell `(b', o') ≠ (b, off)` agrees across `PromoteRel`. -/
theorem PromoteRel.load_other {b : String} {off : Int} {ρ : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) {b' : String} {o' : Int} (hc : ¬ (b' = b ∧ o' = off)) :
    s.load b' o' = t.load b' o' := by
  simp only [JState.load]; exact h.2.2.2 b' o' hc

/-! ### The write helpers: a write to any register `≠ ρ` (with an agreeing value), to any
cell `≠ (b,off)` (with an agreeing value), or a pair of register writes, preserves
`PromoteRel`. These factor the per-instruction step so the 22-arm case split stays linear. -/

/-- `setReg d` to `d ≠ ρ` with an agreeing value preserves `PromoteRel` (and leaves flags
    untouched). -/
theorem PromoteRel.setReg_ne {b : String} {off : Int} {ρ : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) (d : String) (hd : d ≠ ρ) (v : BitVec 64) :
    PromoteRel b off ρ (s.setReg d v) (t.setReg d v) := by
  obtain ⟨hr, hρv, hf, hm⟩ := h
  refine ⟨fun r hrρ => ?_, ?_, hf, hm⟩
  · by_cases hrd : r = d
    · subst hrd; simp [JState.setReg, JState.get]
    · simp only [JState.get, JState.setReg]; rw [if_neg hrd, if_neg hrd]; exact hr r hrρ
  · simp only [JState.get, JState.setReg]; rw [if_neg (Ne.symm hd)]
    simpa [JState.get] using hρv

/-- `writeB5W d` to `d ≠ ρ` with an agreeing `B5W` preserves `PromoteRel`: the data goes to
    `d`, the five flags are overwritten **identically** on both sides, memory is untouched. -/
theorem PromoteRel.writeB5W_ne {b : String} {off : Int} {ρ : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) (d : String) (hd : d ≠ ρ) (tt : B5W 64) :
    PromoteRel b off ρ (s.writeB5W d tt) (t.writeB5W d tt) := by
  obtain ⟨hr, hρv, _hf, hm⟩ := h
  refine ⟨fun r hrρ => ?_, ?_, ?_, ?_⟩
  · by_cases hrd : r = d
    · subst hrd; simp [JState.writeB5W, JState.get]
    · simp only [JState.get, JState.writeB5W]; rw [if_neg hrd, if_neg hrd]; exact hr r hrρ
  · simp only [JState.get, JState.writeB5W]; rw [if_neg (Ne.symm hd)]
    simpa [JState.get] using hρv
  · simp only [JState.writeB5W]
  · intro b' o' hc; simp only [JState.writeB5W]; exact hm b' o' hc

/-- `writeB2W d` to `d ≠ ρ` with an agreeing `B2W` preserves `PromoteRel`: the data goes
    to `d`, `OF`/`CF` are overwritten identically, and the retained `SF`/`PF`/`ZF` agree
    because the pre-state flag states do. -/
theorem PromoteRel.writeB2W_ne {b : String} {off : Int} {ρ : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) (d : String) (hd : d ≠ ρ) (tt : B2W 64) :
    PromoteRel b off ρ (s.writeB2W d tt) (t.writeB2W d tt) := by
  obtain ⟨hr, hρv, hf, hm⟩ := h
  refine ⟨fun r hrρ => ?_, ?_, ?_, ?_⟩
  · by_cases hrd : r = d
    · subst hrd; simp [JState.writeB2W, JState.get]
    · simp only [JState.get, JState.writeB2W]; rw [if_neg hrd, if_neg hrd]; exact hr r hrρ
  · simp only [JState.get, JState.writeB2W]; rw [if_neg (Ne.symm hd)]
    simpa [JState.get] using hρv
  · simp only [JState.writeB2W]; rw [hf]
  · intro b' o' hc; simp only [JState.writeB2W]; exact hm b' o' hc

/-- `writeB5` writes the five flags and no register, so it preserves `PromoteRel`
    with no freshness side condition: `ρ` keeps its value on both sides, the flags
    are overwritten identically, and memory is untouched. -/
theorem PromoteRel.writeB5 {b : String} {off : Int} {ρ : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) (tt : B5W 64) :
    PromoteRel b off ρ (s.writeB5 tt) (t.writeB5 tt) := by
  obtain ⟨hr, hρv, _hf, hm⟩ := h
  refine ⟨fun r hrρ => ?_, ?_, ?_, ?_⟩
  · simpa [JState.writeB5, JState.get] using hr r hrρ
  · simpa [JState.writeB5, JState.get, JState.load] using hρv
  · simp [JState.writeB5]
  · intro b' o' hc; simp only [JState.writeB5]; exact hm b' o' hc

/-- Two register writes (`mulx`/`mulxMem`): both destinations `≠ ρ`, agreeing values. -/
theorem PromoteRel.setReg2_ne {b : String} {off : Int} {ρ : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) (dl dh : String) (hdl : dl ≠ ρ) (hdh : dh ≠ ρ)
    (lo hi : BitVec 64) :
    PromoteRel b off ρ ((s.setReg dl lo).setReg dh hi) ((t.setReg dl lo).setReg dh hi) :=
  ((h.setReg_ne dl hdl lo).setReg_ne dh hdh hi)

/-- A store to a cell `(b', o') ≠ (b, off)` with an agreeing value preserves `PromoteRel`. -/
theorem PromoteRel.store_ne {b : String} {off : Int} {ρ : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) (b' : String) (o' : Int) (hc : ¬ (b' = b ∧ o' = off))
    (v : BitVec 64) :
    PromoteRel b off ρ (s.store b' o' v) (t.store b' o' v) := by
  obtain ⟨hr, hρv, hf, hm⟩ := h
  refine ⟨fun r hrρ => ?_, ?_, ?_, ?_⟩
  · simp only [JState.get, JState.store]; exact hr r hrρ
  · simp only [JState.get, JState.store, JState.load]
    -- (b,off) ≠ (b',o'), so the store at (b',o') leaves cell (b,off) untouched
    have hbo : ¬ (b = b' ∧ off = o') := by
      intro hcon; exact hc ⟨hcon.1.symm, hcon.2.symm⟩
    rw [if_neg hbo]
    simpa [JState.get, JState.load] using hρv
  · simp only [JState.store]; exact hf
  · intro b₂ o₂ hc₂
    simp only [JState.store]
    by_cases hb : b₂ = b' ∧ o₂ = o'
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb]; exact hm b₂ o₂ hc₂

/-! ### The three promotion step lemmas

`promoteCellInstr b off ρ` rewrites only the promoted store / load; everything else is
identity. We prove `PromoteRel` is preserved running the **original** instruction on the
original state `s` and the **promoted** instruction on the promoted state `t`, for each of
the three shapes a promotable cell's instructions take. -/

/-- **Promoted store step.** The original `storeMem b off (.reg r)` writes the cell; the
    promoted `mov ρ r` writes `ρ`. After both, `ρ` (in `t`) holds `r`'s value = the cell (in
    `s`); registers and other cells are untouched; flags unchanged. `r ≠ ρ` (ρ is fresh). -/
theorem PromoteRel.promoted_store {b : String} {off : Int} {ρ r : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) (hrρ : r ≠ ρ) :
    PromoteRel b off ρ (evalInstr s (.storeMem b off (.reg r))) (evalInstr t (.mov ρ (.reg r))) := by
  obtain ⟨hr, _hρv, hf, hm⟩ := h
  simp only [evalInstr, x86_MOV, JOperand.eval]
  refine ⟨fun r' hr'ρ => ?_, ?_, ?_, ?_⟩
  · -- store doesn't touch registers; mov writes ρ ≠ r'
    simp only [JState.get, JState.store, JState.setReg]; rw [if_neg hr'ρ]; exact hr r' hr'ρ
  · -- ρ holds r's value (t); cell holds r's value (s)
    have := (hr r hrρ).symm
    simp only [JState.get, JState.store, JState.setReg, JState.load] at this ⊢
    simpa using this
  · simp only [JState.store, JState.setReg]; exact hf
  · intro b' o' hc; simp only [JState.store, JState.setReg, JState.load]
    rw [if_neg hc]; exact hm b' o' hc

/-- **Promoted load step.** The original `loadMem d b off` reads the cell; the promoted
    `mov d ρ` reads `ρ`. By `PromoteRel`, `ρ` (in `t`) holds the cell value (in `s`), so `d`
    gets the same value; `d ≠ ρ` (ρ fresh) keeps the `ρ↦cell` invariant. -/
theorem PromoteRel.promoted_load {b : String} {off : Int} {ρ d : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) (hdρ : d ≠ ρ) :
    PromoteRel b off ρ (evalInstr s (.loadMem d b off)) (evalInstr t (.mov d (.reg ρ))) := by
  have hρv := h.2.1
  simp only [evalInstr, x86_MOV, JOperand.eval]
  -- `s.setReg d (s.load b off)` vs `t.setReg d (t.get ρ)`; and `t.get ρ = s.load b off`
  have hval : s.load b off = t.get ρ := hρv.symm
  rw [JState.get] at hval ⊢
  rw [← hval]
  -- now both write d the value `s.load b off`
  exact h.setReg_ne d hdρ (s.load b off)

/-- **Kept (transparent) instruction step.** A non-promoted instruction `i` runs unchanged on
    both sides; under `InstrTransparent` (does not name `ρ`, does not read or write the cell)
    `PromoteRel` is preserved. The case split mirrors the model's 22 `evalInstr` arms; each
    reduces to a write helper plus an operand-read equality. -/
theorem PromoteRel.step_transparent {b : String} {off : Int} {ρ : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) (i : JInstr 64) (ht : InstrTransparent b off ρ i) :
    PromoteRel b off ρ (evalInstr s i) (evalInstr t i) := by
  obtain ⟨hwρ, hrρ, hrcell, hwcell, hdyn⟩ := ht
  -- helper to discharge `dst ≠ ρ` from `ρ ∉ writtenRegsI i`
  cases i with
  | mov d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    simp only [evalInstr, x86_MOV]; rw [hsrc]; exact h.setReg_ne d hd _
  | add d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    have hgd : s.get d = t.get d := h.get hd
    simp only [evalInstr]; rw [hsrc, hgd]; exact h.writeB5W_ne d hd _
  | sub d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    have hgd : s.get d = t.get d := h.get hd
    simp only [evalInstr]; rw [hsrc, hgd]; exact h.writeB5W_ne d hd _
  | adc d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    have hgd : s.get d = t.get d := h.get hd
    have hcf := h.flagB (·.cf)
    simp only [evalInstr]; rw [hsrc, hgd, hcf]; exact h.writeB5W_ne d hd _
  | sbb d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    have hgd : s.get d = t.get d := h.get hd
    have hcf := h.flagB (·.cf)
    simp only [evalInstr]; rw [hsrc, hgd, hcf]; exact h.writeB5W_ne d hd _
  | imul d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    have hgd : s.get d = t.get d := h.get hd
    simp only [evalInstr]; rw [hsrc, hgd]; exact h.writeB5W_ne d hd _
  | neg d =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hgd : s.get d = t.get d := h.get hd
    simp only [evalInstr]; rw [hgd]; exact h.writeB5W_ne d hd _
  | setc d =>
    -- `setc d := if CF then 1 else 0`: writes only `d` (≠ ρ, fresh) from the carry
    -- flag (equal in s,t by `h.flagB`); `setReg_ne` preserves `PromoteRel`.
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hcf := h.flagB (·.cf)
    simp only [evalInstr]; rw [hcf]; exact h.setReg_ne d hd _
  | and_ d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    have hgd : s.get d = t.get d := h.get hd
    simp only [evalInstr]; rw [hsrc, hgd]; exact h.writeB5W_ne d hd _
  | test a src =>
    -- No destination: `a` is a read, so its disequality with `ρ` comes from
    -- `readRegs`, not `writtenRegsI`, and the write helper needs no freshness.
    have haρ : a ≠ ρ := by
      intro hc; subst hc; exact hrρ (by simp [readRegs])
    have hsrcρ : ρ ∉ srcNames src := by
      simp only [readRegs, List.mem_cons, not_or] at hrρ; exact hrρ.2
    have hsrc := h.reg_read src hsrcρ
    have hga : s.get a = t.get a := h.get haρ
    simp only [evalInstr]; rw [hsrc, hga]; exact h.writeB5 _
  | cmp a src =>
    -- as `test`: `a` is a read and the write is the five flags alone.
    have haρ : a ≠ ρ := by
      intro hc; subst hc; exact hrρ (by simp [readRegs])
    have hsrcρ : ρ ∉ srcNames src := by
      simp only [readRegs, List.mem_cons, not_or] at hrρ; exact hrρ.2
    have hsrc := h.reg_read src hsrcρ
    have hga : s.get a = t.get a := h.get haρ
    simp only [evalInstr]; rw [hsrc, hga]; exact h.writeB5 _
  | not_ d =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hgd : s.get d = t.get d := h.get hd
    simp only [evalInstr]; rw [hgd]; exact h.setReg_ne d hd _
  | andn d a c =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have haρ : a ≠ ρ := by intro hc; subst hc; exact hrρ (by simp [readRegs])
    have hcρ : c ≠ ρ := by intro hc; subst hc; exact hrρ (by simp [readRegs])
    have hga : s.get a = t.get a := h.get haρ
    have hgc : s.get c = t.get c := h.get hcρ
    simp only [evalInstr]; rw [hga, hgc]; exact h.writeB5W_ne d hd _
  | rol d amt =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrcρ : ρ ∉ srcNames amt := by
      simp only [readRegs, List.mem_cons, not_or] at hrρ; exact hrρ.2
    have hsrc := h.reg_read amt hsrcρ
    have hgd : s.get d = t.get d := h.get hd
    simp only [evalInstr]; rw [hsrc, hgd]; exact h.writeB2W_ne d hd _
  | ror d amt =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrcρ : ρ ∉ srcNames amt := by
      simp only [readRegs, List.mem_cons, not_or] at hrρ; exact hrρ.2
    have hsrc := h.reg_read amt hsrcρ
    have hgd : s.get d = t.get d := h.get hd
    simp only [evalInstr]; rw [hsrc, hgd]; exact h.writeB2W_ne d hd _
  | rorx d src amt =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hvρ : src ≠ ρ := by intro hc; subst hc; exact hrρ (by simp [readRegs])
    have hsrcρ : ρ ∉ srcNames amt := by
      simp only [readRegs, List.mem_cons, not_or] at hrρ; exact hrρ.2
    have hsrc := h.reg_read amt hsrcρ
    have hgv : s.get src = t.get src := h.get hvρ
    simp only [evalInstr]; rw [hsrc, hgv]; exact h.setReg_ne d hd _
  | shlx d src c =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hvρ : src ≠ ρ := by intro hc; subst hc; exact hrρ (by simp [readRegs])
    have hcρ : c ≠ ρ := by intro hc; subst hc; exact hrρ (by simp [readRegs])
    simp only [evalInstr]; rw [h.get hvρ, h.get hcρ]; exact h.setReg_ne d hd _
  | shrx d src c =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hvρ : src ≠ ρ := by intro hc; subst hc; exact hrρ (by simp [readRegs])
    have hcρ : c ≠ ρ := by intro hc; subst hc; exact hrρ (by simp [readRegs])
    simp only [evalInstr]; rw [h.get hvρ, h.get hcρ]; exact h.setReg_ne d hd _
  | sarx d src c =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hvρ : src ≠ ρ := by intro hc; subst hc; exact hrρ (by simp [readRegs])
    have hcρ : c ≠ ρ := by intro hc; subst hc; exact hrρ (by simp [readRegs])
    simp only [evalInstr]; rw [h.get hvρ, h.get hcρ]; exact h.setReg_ne d hd _
  | movzx d sw src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hvρ : src ≠ ρ := by intro hc; subst hc; exact hrρ (by simp [readRegs])
    simp only [evalInstr]; rw [h.get hvρ]; exact h.setReg_ne d hd _
  | movsx d sw src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hvρ : src ≠ ρ := by intro hc; subst hc; exact hrρ (by simp [readRegs])
    simp only [evalInstr]; rw [h.get hvρ]; exact h.setReg_ne d hd _
  | lea d bs ix sc dsp =>
    -- an address computation over two register reads; no cell is read or written, so
    -- the promoted cell's invariant is untouched.
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hbρ : bs ≠ ρ := by intro hc; subst hc; exact hrρ (by simp [readRegs])
    have hiρ : ix ≠ ρ := by intro hc; subst hc; exact hrρ (by simp [readRegs])
    simp only [evalInstr]; rw [h.get hbρ, h.get hiρ]; exact h.setReg_ne d hd _
  | or_ d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    have hgd : s.get d = t.get d := h.get hd
    simp only [evalInstr]; rw [hsrc, hgd]; exact h.writeB5W_ne d hd _
  | xor_ d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    have hgd : s.get d = t.get d := h.get hd
    simp only [evalInstr]; rw [hsrc, hgd]; exact h.writeB5W_ne d hd _
  | shl d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    have hgd : s.get d = t.get d := h.get hd
    simp only [evalInstr]; rw [hsrc, hgd]; exact h.writeB5W_ne d hd _
  | shr d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    have hgd : s.get d = t.get d := h.get hd
    simp only [evalInstr]; rw [hsrc, hgd]; exact h.writeB5W_ne d hd _
  | sar d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    have hgd : s.get d = t.get d := h.get hd
    simp only [evalInstr]; rw [hsrc, hgd]; exact h.writeB5W_ne d hd _
  | cmove d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrcρ : ρ ∉ srcNames src := by
      simp only [readRegs, List.mem_cons, not_or] at hrρ; exact hrρ.2
    have hsrc := h.reg_read src hsrcρ
    have hgd : s.get d = t.get d := h.get hd
    have hzf := h.flagB (·.zf)
    simp only [evalInstr]; rw [hsrc, hgd, hzf]; exact h.setReg_ne d hd _
  | cmovne d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrcρ : ρ ∉ srcNames src := by
      simp only [readRegs, List.mem_cons, not_or] at hrρ; exact hrρ.2
    have hsrc := h.reg_read src hsrcρ
    have hgd : s.get d = t.get d := h.get hd
    have hzf := h.flagB (·.zf)
    simp only [evalInstr]; rw [hsrc, hgd, hzf]; exact h.setReg_ne d hd _
  | cmovb d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrcρ : ρ ∉ srcNames src := by
      simp only [readRegs, List.mem_cons, not_or] at hrρ; exact hrρ.2
    have hsrc := h.reg_read src hsrcρ
    have hgd : s.get d = t.get d := h.get hd
    have hcf := h.flagB (·.cf)
    simp only [evalInstr]; rw [hsrc, hgd, hcf]; exact h.setReg_ne d hd _
  | mulx dh dl a c =>
    have hdh : dh ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hdl : dl ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hra : a.eval s = a.eval t := h.reg_read a (by simp only [readRegs] at hrρ; intro hc; exact hrρ (List.mem_append_left _ hc))
    have hrc : c.eval s = c.eval t := h.reg_read c (by simp only [readRegs] at hrρ; intro hc; exact hrρ (List.mem_append_right _ hc))
    simp only [evalInstr]; rw [hra, hrc]; exact h.setReg2_ne dl dh hdl hdh _ _
  | mulxMem dh dl a base o =>
    have hdh : dh ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hdl : dl ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hra : a.eval s = a.eval t := h.reg_read a (by simpa [readRegs] using hrρ)
    have hcellne : ¬ (base = b ∧ o = off) := by
      intro hc; exact hrcell (by simp only [readCell]; rw [hc.1, hc.2])
    have hcell : s.load base o = t.load base o := h.load_other hcellne
    simp only [evalInstr]; rw [hra, hcell]; exact h.setReg2_ne dl dh hdl hdh _ _
  | adcx d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    have hgd : s.get d = t.get d := h.get hd
    have hcf := h.flagB (·.cf)
    obtain ⟨hr, hρv, hflags, hm⟩ := h
    simp only [evalInstr]; rw [hsrc, hgd, hcf]
    refine ⟨fun r hrρ => ?_, ?_, ?_, ?_⟩
    · by_cases hrd : r = d
      · subst hrd; simp [JState.get]
      · simp only [JState.get]; rw [if_neg hrd, if_neg hrd]; exact hr r hrρ
    · simp only [JState.get]; rw [if_neg (Ne.symm hd)]; simpa [JState.get] using hρv
    · simp only []; rw [hflags]
    · intro b' o' hc; exact hm b' o' hc
  | adox d src =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    have hgd : s.get d = t.get d := h.get hd
    have hof := h.flagB (·.of)
    obtain ⟨hr, hρv, hflags, hm⟩ := h
    simp only [evalInstr]; rw [hsrc, hgd, hof]
    refine ⟨fun r hrρ => ?_, ?_, ?_, ?_⟩
    · by_cases hrd : r = d
      · subst hrd; simp [JState.get]
      · simp only [JState.get]; rw [if_neg hrd, if_neg hrd]; exact hr r hrρ
    · simp only [JState.get]; rw [if_neg (Ne.symm hd)]; simpa [JState.get] using hρv
    · simp only []; rw [hflags]
    · intro b' o' hc; exact hm b' o' hc
  | loadMem d base o =>
    have hd : d ≠ ρ := fun hc => hwρ (by simp [InstrTransparent.writtenRegsI, hc])
    have hcellne : ¬ (base = b ∧ o = off) := by
      intro hc; exact hrcell (by simp only [readCell]; rw [hc.1, hc.2])
    have hcell : s.load base o = t.load base o := h.load_other hcellne
    simp only [evalInstr, x86_MOV]; rw [hcell]; exact h.setReg_ne d hd _
  | storeMem base o src =>
    have hcellne : ¬ (base = b ∧ o = off) := by
      intro hc; exact hwcell (by simp only [writeCell]; rw [hc.1, hc.2])
    have hsrc := h.reg_read src (by simpa [readRegs] using hrρ)
    simp only [evalInstr, x86_MOV]; rw [hsrc]; exact h.store_ne base o hcellne _
  -- A transparent instruction is never an indexed (dynamic-address) read/write: those carry
  -- `readsDynamic = true`, contradicting the `InstrTransparent` conjunct `hdyn`.
  | loadMemIdx d base' idx scale => simp [readsDynamic] at hdyn
  | storeMemIdx base' idx scale src => simp [readsDynamic] at hdyn
  -- `loadSym` re-aliases a memory bank, so it carries `readsDynamic = true` and is
  -- likewise excluded by the `InstrTransparent` conjunct `hdyn`.
  | loadSym d sym => simp [readsDynamic] at hdyn

/-! ### Per-instruction classification of a promotable cell's instructions

`PromotableInstr b off ρ i` says `i` is one the three shapes a sound promotion of `(b,off)`
to fresh register `ρ` admits: the **promoted store** `storeMem b off (.reg r)` (`r ≠ ρ`), a
**promoted load** `loadMem d b off` (`d ≠ ρ`), or a **transparent** instruction. For each, the
promoted instruction `promoteCellInstr b off ρ i` runs (on the promoted state) so as to
preserve `PromoteRel` against `i` on the original state — the per-instruction soundness
certificate that lifts over `runBlock`. -/
inductive PromotableInstr (b : String) (off : Int) (ρ : String) : JInstr 64 → Prop
  | promotedStore (r : String) (hr : r ≠ ρ) : PromotableInstr b off ρ (.storeMem b off (.reg r))
  | promotedLoad (d : String) (hd : d ≠ ρ) : PromotableInstr b off ρ (.loadMem d b off)
  | transparent (i : JInstr 64) (ht : InstrTransparent b off ρ i) : PromotableInstr b off ρ i

/-- **Unified one-instruction soundness.** Under `PromotableInstr`, running `i` on the
    original state `s` and the promoted instruction `promoteCellInstr b off ρ i` on the
    promoted state `t` preserves `PromoteRel`. -/
theorem PromoteRel.promoteCellInstr_step {b : String} {off : Int} {ρ : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) {i : JInstr 64} (hi : PromotableInstr b off ρ i) :
    PromoteRel b off ρ (evalInstr s i) (evalInstr t (promoteCellInstr b off ρ i)) := by
  cases hi with
  | promotedStore r hr =>
    -- `promoteCellInstr` on `storeMem b off (.reg r)` (matching cell) ↦ `mov ρ (.reg r)`
    have hpc : promoteCellInstr b off ρ (.storeMem b off (.reg r)) = .mov ρ (.reg r) := by
      simp [promoteCellInstr]
    rw [hpc]; exact h.promoted_store hr
  | promotedLoad d hd =>
    have hpc : promoteCellInstr b off ρ (.loadMem d b off) = .mov d (.reg ρ) := by
      simp [promoteCellInstr]
    rw [hpc]; exact h.promoted_load hd
  | transparent i ht =>
    -- `promoteCellInstr` leaves a transparent instruction unchanged (it is not a matching
    -- promoted store/load: the cell-mismatch arms reduce to the identity).
    have hpc : promoteCellInstr b off ρ i = i := by
      obtain ⟨_, _, hrcell, hwcell, _⟩ := ht
      cases i with
      | storeMem base o src =>
        cases src with
        | reg r =>
          simp only [promoteCellInstr]
          have : ¬ (base = b ∧ o = off) := fun hc =>
            hwcell (by simp only [writeCell]; rw [hc.1, hc.2])
          rw [if_neg this]
        | imm v => simp [promoteCellInstr]
      | loadMem d base o =>
        simp only [promoteCellInstr]
        have : ¬ (base = b ∧ o = off) := fun hc =>
          hrcell (by simp only [readCell]; rw [hc.1, hc.2])
        rw [if_neg this]
      | _ => rfl
    rw [hpc]; exact h.step_transparent i ht

/-! ### Lift over the whole block: `BlockPromotable` + the `runBlock` agreement

A block is **promotable** for `(b, off, ρ)` when every instruction is `PromotableInstr`. We
require the **freshness** of `ρ` and the **no-mulxMem / loadMem-only / register-source-store**
discipline through `InstrTransparent` (which forbids reading `(b, off)` by anything other than
the rewritten `loadMem`, in particular forbids a `mulxMem` at `(b, off)` — the #416 bug). -/
def BlockPromotable (b : String) (off : Int) (ρ : String) (block : List (JInstr 64)) : Prop :=
  ∀ i ∈ block, PromotableInstr b off ρ i

/-- **Whole-body promotion soundness (single cell).** If `block` is promotable for `(b,off,ρ)`
    then for any pair of states related by `PromoteRel`, `runBlock` of the original and of the
    promoted block stay `PromoteRel`-related. By induction on the block via the per-instruction
    step. -/
theorem PromoteRel.promoteCell_runBlock {b : String} {off : Int} {ρ : String}
    (block : List (JInstr 64)) (hb : BlockPromotable b off ρ block) {s t : JState 64}
    (h : PromoteRel b off ρ s t) :
    PromoteRel b off ρ (runBlock s block) (runBlock t (promoteCell b off ρ block)) := by
  induction block generalizing s t with
  | nil => simpa [promoteCell] using h
  | cons i is ih =>
    simp only [promoteCell, List.map_cons, runBlock_cons]
    have hi : PromotableInstr b off ρ i := hb i (List.mem_cons_self ..)
    have hstep := h.promoteCellInstr_step hi
    exact ih (fun j hj => hb j (List.mem_cons_of_mem _ hj)) hstep

/-- **Initial relatedness.** A fresh register `ρ` that the block never names starts
    `PromoteRel`-related to *any* state once we set `ρ`'s initial value to the cell's: at the
    function entry the harness has not written `(b, off)` (a scratch slot) nor `ρ`, so we begin
    from `s` and `s.setReg ρ (s.load b off)`. (For the closed application the cell starts `0`
    and `ρ` is initialised to match; the relation is established by construction here.) -/
theorem PromoteRel.init (b : String) (off : Int) (ρ : String) (s : JState 64) :
    PromoteRel b off ρ s (s.setReg ρ (s.load b off)) := by
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [JState.get, JState.setReg]; rw [if_neg hr]
  · simp [JState.get, JState.setReg, JState.load]
  · rfl
  · intro b' o' _; rfl

/-- A `PromoteRel` between two states yields `AgreeOn prot` whenever the promoted cell
    `(b, off)` is **not** protected: registers other than `ρ` agree (and `ρ` is a fresh
    promotion register that is not a harness output, so it is excluded from the observable
    footprint by being absent from `prot` and from the register comparison the harness uses);
    every protected cell ≠ `(b, off)` agrees. We expose the **memory-only** agreement, which is
    what the harness observes (it reads the ladder coordinate cells, not `ρ`). -/
theorem PromoteRel.protectedCellsAgree {b : String} {off : Int} {ρ : String} {s t : JState 64}
    (h : PromoteRel b off ρ s t) (prot : List (String × Int))
    (hp : (b, off) ∉ prot) :
    ∀ c ∈ prot, s.load c.1 c.2 = t.load c.1 c.2 := by
  intro c hc
  have hcne : ¬ (c.1 = b ∧ c.2 = off) := by
    intro hcon
    have : c = (b, off) := by rw [Prod.ext_iff]; exact hcon
    rw [this] at hc; exact hp hc
  simp only [JState.load]; exact h.2.2.2 c.1 c.2 hcne

/-- **Whole-body single-cell promotion preserves every protected output cell.** Running the
    promoted block from `ρ`-initialised state `t = s.setReg ρ (s.load b off)` lands in a state
    agreeing with `runBlock s block` on every protected cell (the harness-observable ladder
    coordinates), provided the block is promotable and `(b, off)` is unprotected scratch. This
    is the in-Lean translation-validation certificate for one promoted scratch cell — proved,
    not KAT-gated. -/
theorem promoteCell_protected_runBlock {b : String} {off : Int} {ρ : String}
    (block : List (JInstr 64)) (prot : List (String × Int))
    (hb : BlockPromotable b off ρ block) (hp : (b, off) ∉ prot) (s : JState 64) :
    ∀ c ∈ prot,
      (runBlock s block).load c.1 c.2
        = (runBlock (s.setReg ρ (s.load b off)) (promoteCell b off ρ block)).load c.1 c.2 :=
  ((PromoteRel.init b off ρ s).promoteCell_runBlock block hb).protectedCellsAgree prot hp

end CatCrypt.Crypto.Optimizer.Mem2Reg
