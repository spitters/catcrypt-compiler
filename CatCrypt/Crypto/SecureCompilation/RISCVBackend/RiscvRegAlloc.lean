/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvAsmPrinter
import CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-!
# A fresh RV64 register allocator as a `MachineModel` instance of the generic pass (#552)

`Optimizer.GenericRegAlloc` (#552) factored the x86 `SpillingRegAlloc` and the A64
`ArmRegAlloc` into a single `MachineModel`-parameterized validated allocator: the
linear-scan allocator (untrusted) + the verified checker (the injective-renaming
keystone `renameBlock_runBlock`, the spill-store/reload-roundtrip sandwich
`reload_sandwich`, the rewrite-length decomposition `rewriteBlock_length`), all stated
**once** over `[RegMachine I S]` / `[MemMachine M]`.

This module **instantiates that generic pass fresh for RISC-V RV64** — the backend that
had *no* register allocator and therefore emitted SHA-256 fully stack-resident (every
SSA name a 4-byte slot off `a0`, each `RInst` an `lw`-source → op → `sw`-dst storm: the
llvm-mca-sifive-u74 estimate is `37829` cyc, base RV64I, vs clang-O3's `2051` — the 18×
gap). The instance:

* `instMachineModelRInst` (`MachineModel RInst`): `writtenName`/`readNames` from
  `rinstDstSrcs`, the RV64 GP file `physRegs` (`a0..a7,t0..t6,s0..s11` minus the two
  pinned `a0`/scratch), and `mkSpill`/`mkReload` rendered as `sw`/`lw`.
* `instRegMachineRInst` (`RegMachine RInst RState`): the per-op `evalRInst` is a single
  `set d (instVal s i)` write (`evalRInst_eq_set`), `runRBlock` is the left fold, and
  the source-locality `instVal_rename` holds by `cases` over `RInst` — so the generic
  `renameBlock_runBlock` keystone **specializes** to the RV64 register-resident path.
* `instMemMachineRMemState` (`MemMachine RMemState`): the spill path over a
  memory-extended `RState`, so the generic `spillStore_establishes` / `evalReload_noop`
  / `reload_sandwich` give the RV64 spill soundness.

The deliverable is the fresh instance plus the register-resident SHA-256 re-emit it
enables (`bench/riscv_compare/sha256_rv64_ra_emit.lean`): the verified ops are
unchanged, only the storage class of each value changes (resident in a GP register vs
spilled to a frame cell), and the value identity is the qemu-riscv64 FIPS-180-4 KAT.
The A64 twin (`ArmRegAlloc`, #551) closed the analogous SHA-256 5.42× → 2.00×.

No `sorry`; the generic keystones carry no custom axioms (RV64 `instVal_rename` is by
`cases`, the spill laws by the `RMemState` projections).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRegAlloc

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-! ## 1. Renaming an `RInst` + the per-op value function

The RV64 analogue of `ArmRegAlloc.renameAInst` / `instVal`: apply a renaming `ρ` to an
instruction's dst + sources, and the value it writes as a function of the state. -/

/-- Apply a renaming `ρ` to one `RInst` (rename dst and all sources). -/
def renameRInst (ρ : String → String) : RInst → RInst
  | .addw d a b => .addw (ρ d) (ρ a) (ρ b)
  | .subw d a b => .subw (ρ d) (ρ a) (ρ b)
  | .and  d a b => .and  (ρ d) (ρ a) (ρ b)
  | .or   d a b => .or   (ρ d) (ρ a) (ρ b)
  | .xor  d a b => .xor  (ρ d) (ρ a) (ρ b)
  | .slliw d a m => .slliw (ρ d) (ρ a) m
  | .srliw d a m => .srliw (ρ d) (ρ a) m
  | .roriw d a m => .roriw (ρ d) (ρ a) m
  | .mv   d s    => .mv   (ρ d) (ρ s)

/-- The value an `RInst` writes to its destination, as a function of the state. -/
def instValR (s : RState) : RInst → R32
  | .addw _ a b => opAddw (s.get a) (s.get b)
  | .subw _ a b => opSubw (s.get a) (s.get b)
  | .and  _ a b => opAnd (s.get a) (s.get b)
  | .or   _ a b => opOr  (s.get a) (s.get b)
  | .xor  _ a b => opXor (s.get a) (s.get b)
  | .slliw _ a m => opSlliw (s.get a) m
  | .srliw _ a m => opSrliw (s.get a) m
  | .roriw _ a m => opRoriw (s.get a) m
  | .mv   _ a   => s.get a

/-- `evalRInst s i = s.set (writtenName i) (instValR s i)`: every op is a single write
    of `instValR` to the destination — the shape the `RegMachine` class needs. -/
theorem evalRInst_eq_set (s : RState) (i : RInst) :
    evalRInst s i = s.set (rinstDstSrcs i).1 (instValR s i) := by
  cases i <;> rfl

/-- The renamed op writes `ρ (writtenName i)`. -/
theorem writtenName_renameRInst (ρ : String → String) (i : RInst) :
    (rinstDstSrcs (renameRInst ρ i)).1 = ρ (rinstDstSrcs i).1 := by
  cases i <;> rfl

/-- **The renamed op writes the same value**, given that every source read agrees via
    `ρ`. By `cases` over `RInst`: `instValR` reads only the read-names, so if `t` at
    `ρ a` equals `s` at `a` for every source `a`, the values coincide. -/
theorem instValR_rename (ρ : String → String) (s t : RState) (i : RInst)
    (h : ∀ a ∈ (rinstDstSrcs i).2, t.get (ρ a) = s.get a) :
    instValR t (renameRInst ρ i) = instValR s i := by
  cases i <;>
    simp only [renameRInst, instValR, rinstDstSrcs, List.mem_cons,
      forall_eq_or_imp] at h ⊢ <;>
    (try obtain ⟨ha, hb⟩ := h) <;>
    simp_all

/-! ## 2. The RV64 GP register file (the `physRegs` pool)

RV64 has 32 integer registers; the SHA-256 register-resident emit allocates from the
caller-saved temporaries + saved registers, keeping `a0` (the argument-buffer pointer)
pinned and `t0`/`t1` reserved as reload scratch — the RV64 analogue of the A64 pool
`w0..w30` minus `x1`/`w16`/`w17`. -/

/-- The two reserved scratch registers a reloaded spill value is materialised into
    (`t0`/`t1`, caller-saved — the same the stack-resident emit uses). Two suffice: a
    binary op reads at most two sources. -/
def workRegs : List String := ["t0", "t1"]

/-- The full RV64 allocatable GP file at 32-bit `*W` width: the caller-saved temporaries
    `t2..t6`, argument registers `a1..a7` (a0 is the pinned buffer pointer), and the
    callee-saved `s0..s11` — 24 registers, ample for the SHA-256 working set. -/
def gpFile : List String :=
  (List.range 5).map (fun i => "t" ++ toString (i + 2)) ++   -- t2..t6
  (List.range 7).map (fun i => "a" ++ toString (i + 1)) ++   -- a1..a7
  (List.range 12).map (fun i => "s" ++ toString i)           -- s0..s11

/-! ## 3. The `MachineModel` / `RegMachine` / `MemMachine` instances (the fresh wiring)

The genuine deliverable: instantiating the generic pass for RV64. -/

/-- **`MachineModel RInst`**: the syntactic interface — written/read names from
    `rinstDstSrcs`, the GP file, and `sw`/`lw` as the spill/reload constructors. -/
instance instMachineModelRInst : MachineModel RInst where
  writtenNames i := [(rinstDstSrcs i).1]
  readNames i := (rinstDstSrcs i).2
  physRegs := gpFile
  -- a spill store / reload load are themselves `RInst`-shaped markers; the printer
  -- renders them as `sw r, off(a0)` / `lw r, off(a0)`. We model them at the op level
  -- as a `mv` carrying the name (the printer attaches the frame offset), matching the
  -- A64 `ArmRegAlloc` `Item.spill` posture.
  mkSpill r _off := .mv r r
  mkReload r _off := .mv r r

/-- **`RegMachine RInst RState`**: the semantic interface — `runRBlock`, the 32-bit
    register file, and the per-op shape. The generic `renameBlock_runBlock` keystone
    specializes through this instance to the RV64 register-resident path. -/
instance instRegMachineRInst : RegMachine RInst RState where
  toMachineModel := instMachineModelRInst
  runBlock := runRBlock
  Val := R32
  get := RState.get
  set := RState.set
  -- RV64 discards writes to BOTH `zero` and its numeric spelling `x0` (the model
  -- treats them identically); the discard predicate names the whole set.
  isDiscard r := r == "zero" || r == "x0"
  writes s i := [((rinstDstSrcs i).1, instValR s i)]
  renameInst := renameRInst
  get_discard s s' r r' hr hr' := by
    have hr2 : r = "zero" ∨ r = "x0" := by
      rcases (by simpa [or_assoc] using hr : r = "zero" ∨ r = "x0") with h | h <;> simp [h]
    have hr2' : r' = "zero" ∨ r' = "x0" := by
      rcases (by simpa [or_assoc] using hr' : r' = "zero" ∨ r' = "x0") with h | h <;> simp [h]
    simp only [RState.get]
    rw [if_pos hr2, if_pos hr2']
  get_set_same s r v h := by
    have : ¬ (r = "zero" ∨ r = "x0") := by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
      exact fun hc => hc.elim h.1 h.2
    exact RState.get_set_same s r v this
  get_set_other s r r' v h := RState.get_set_other s r' r v (Ne.symm h)
  evalInst_eq_set s i r := congrArg (fun st => RState.get st r) (by simpa using evalRInst_eq_set s i)
  runBlock_nil := runRBlock_nil
  runBlock_append s xs ys := runRBlock_append_model s xs ys
  writes_names s i := rfl
  writes_rename ρ s t i h := by
    show [((rinstDstSrcs (renameRInst ρ i)).1, instValR t (renameRInst ρ i))]
      = [(ρ (rinstDstSrcs i).1, instValR s i)]
    rw [instValR_rename ρ s t i h, writtenName_renameRInst ρ i]

/-! ### The memory-extended RV64 state for the spill path

A `RState` plus a frame memory keyed by byte offset — the RV64 analogue of the A64
`AMemState`. The `MemMachine` instance gives the generic spill/reload soundness. -/

/-- A memory-extended RV64 state: the register file plus a frame memory. -/
structure RMemState where
  /-- The register file. -/
  st : RState
  /-- The frame memory (byte offset → 32-bit word). -/
  mem : Int → R32

namespace RMemState

/-- Read a register. -/
def get (m : RMemState) (r : String) : R32 := m.st.get r
/-- Read a frame cell. -/
def load (m : RMemState) (off : Int) : R32 := m.mem off
/-- Write a register. -/
def setReg (m : RMemState) (r : String) (v : R32) : RMemState := { m with st := m.st.set r v }
/-- Write a frame cell. -/
def store (m : RMemState) (off : Int) (v : R32) : RMemState :=
  { m with mem := fun o => if o = off then v else m.mem o }

theorem load_store_same (m : RMemState) (off : Int) (v : R32) :
    (m.store off v).load off = v := by simp [store, load]

theorem load_store_other (m : RMemState) (off o : Int) (v : R32) (h : o ≠ off) :
    (m.store off v).load o = m.load o := by simp [store, load, h]

theorem get_store (m : RMemState) (off : Int) (v : R32) (r : String) :
    (m.store off v).get r = m.get r := by simp [store, get]

/-- `RState.set s r (s.get r) = s`: writing a register a value it already holds is a
    no-op (the RV64 register-file idempotence). -/
theorem RState.set_get_self (s : RState) (r : String) : s.set r (s.get r) = s := by
  by_cases hz : r = "zero" ∨ r = "x0"
  · simp only [RState.set, hz, if_true]
  · simp only [RState.get, hz, if_false, RState.set]
    congr 1
    funext r'
    by_cases h : r' = r <;> simp [h]

theorem setReg_get_self (m : RMemState) (r : String) : m.setReg r (m.get r) = m := by
  unfold setReg get
  cases m with
  | mk st mem => simp only [RState.set_get_self]

end RMemState

/-- **`MemMachine RMemState`**: the spill-path interface, so the generic
    `spillStore_establishes` / `evalReload_noop` / `reload_sandwich` give the RV64 spill
    soundness. -/
instance instMemMachineRMemState : MemMachine RMemState where
  Val := R32
  get := RMemState.get
  load := RMemState.load
  setReg := RMemState.setReg
  store := RMemState.store
  load_store_same := RMemState.load_store_same
  load_store_other := RMemState.load_store_other
  get_store := RMemState.get_store
  setReg_get_self := RMemState.setReg_get_self

/-! ## 4. The generic keystones, specialized to RV64 (the abstraction validated)

The point of the instance: the generic lemmas, instantiated at `RInst`/`RState`, give
the RV64 register-allocation soundness *for free* — no re-proof. These re-export the
generic results at the RV64 types as the canonical RV64 RA soundness statements. -/

/-- **RV64 resident-path soundness** — `GenericRegAlloc.renameBlock_runBlock`
    instantiated at `RInst`/`RState`: applying an injective renaming `ρ` that maps the
    RV64 discard set `{zero, x0}` to itself (and real names to real registers) onto an
    `RInst` block commutes with `runRBlock`. The RV64 register-resident keystone,
    obtained from the generic pass with no new proof. -/
theorem renameRBlock_runRBlock (ρ : String → String) (hinj : Function.Injective ρ)
    (hρd : ∀ r, rmDisc RInst RState r = true → rmDisc RInst RState (ρ r) = true)
    (hρnd : ∀ r, rmDisc RInst RState r = false → rmDisc RInst RState (ρ r) = false)
    (block : List RInst)
    (hz : ∀ i ∈ block, rmDisc RInst RState (rinstDstSrcs i).1 = false)
    (s t : RState) (h : Reindexed RInst ρ s t) :
    Reindexed RInst ρ (rmRun RInst s block) (rmRun RInst t (renameBlock (S := RState) ρ block)) :=
  renameBlock_runBlock RInst ρ hinj hρd hρnd block
    (fun i hi n hn => by
      have hn' : n = (rinstDstSrcs i).1 := by
        simpa [MachineModel.writtenNames, instMachineModelRInst] using hn
      exact hn' ▸ hz i hi) s t h

/-- **RV64 spill-store establishes the cell↦reg invariant** —
    `GenericRegAlloc.spillStore_establishes` at `RMemState`. -/
theorem riscv_spillStore_establishes (m : RMemState) (off : Int) (r : String) :
    SpillValid off r (evalSpillStore m off r) :=
  spillStore_establishes m off r

/-- **RV64 reload is a no-op under `SpillValid`** —
    `GenericRegAlloc.reload_sandwich` at `RMemState`. -/
theorem riscv_reload_sandwich (m : RMemState) (off : Int) (r : String)
    (hv : SpillValid off r m) : evalReload m r off = m :=
  reload_sandwich m off r hv

/-- **RV64 rewrite-length decomposition** — `GenericRegAlloc.rewriteBlock_length` at
    `RInst`: the register-allocated block is one machine instruction per op plus exactly
    the inserted spill traffic. -/
theorem riscv_rewriteBlock_length (decisions : List (String × Slot)) (block : List RInst) :
    (rewriteBlock decisions block).length
      = block.length + reloadCount decisions block + storeCount decisions block :=
  rewriteBlock_length decisions block

/-! ## 5. Live-range / allocator sanity (testable)

The generic live-range analysis + linear scan, run on the RV64 `MachineModel RInst`
instance: confirming the instance is non-vacuous and the allocator spills under
pressure (the capability the printer's non-spilling `allocGp` lacks). -/

/-- A toy RV64 body: `t := a + b`, `r := t + c`, `u := t + r` — `t` is live across the
    whole body. -/
def sanityBody : List RInst :=
  [ .addw "t" "a" "b", .addw "r" "t" "c", .addw "u" "t" "r" ]

/-- `t`'s live range is `[def=0, lastUse=2]`, non-empty and within the body. -/
theorem sanity_t_liverange :
    defIdxOf sanityBody "t" = 0 ∧ lastUseIdx sanityBody "t" = 2
      ∧ defIdxOf sanityBody "t" ≤ lastUseIdx sanityBody "t" := by native_decide

/-- Every name's live range lies within the body with `def ≤ lastUse`. -/
theorem sanity_liveranges_wellformed :
    (liveRanges sanityBody).all
      (fun lr => lr.defIdx ≤ lr.lastUse ∧ lr.lastUse < sanityBody.length) = true := by
  native_decide

/-- 6 names all live to the end — peak pressure 6. -/
def hotBody : List RInst :=
  [ .mv "a" "i1", .mv "b" "i2", .mv "c" "i3", .mv "d" "i4", .mv "e" "i5", .mv "f" "i6"
  , .addw "a" "a" "b", .addw "a" "a" "c", .addw "a" "a" "d", .addw "a" "a" "e", .addw "a" "a" "f" ]

/-- The allocatable RV64 pool, restricted to a 3-register slice (pin all but
    `t2`/`a1`/`a2`) — smaller than the 6-name peak pressure, forcing a spill. -/
def tinyPool : List String := ["t2", "a1", "a2"]

/-- **The generic allocator spills** on the over-budget RV64 body: with a pool smaller
    than the peak pressure it produces at least one `spilled` decision — the capability
    the printer's non-spilling `allocGp` (which truncates to `<UNALLOCATED>`) lacks. -/
theorem hot_spillAlloc_spills :
    0 < spillCount (linearScan tinyPool 0 (liveRanges hotBody)) := by native_decide

/-- Every decision is well-formed (a register or a non-negative frame offset). -/
theorem hot_spillAlloc_wellformed :
    (linearScan tinyPool 0 (liveRanges hotBody)).all
      (fun d => match d.2 with | .resident _ => true | .spilled off => 0 ≤ off) = true := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRegAlloc
