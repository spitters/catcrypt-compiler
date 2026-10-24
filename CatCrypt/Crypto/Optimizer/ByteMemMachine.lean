/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-!
# A byte-addressed spill memory: the non-interference law carries a width

`GenericRegAlloc.MemMachine` indexes the spill frame by a **cell** — one cell per
full-width value — so its non-interference law `load_store_other` asks only for
`o ≠ off`. A `%ymm` value is 32 bytes wide, and the frame offsets `0` and `8` are
distinct with overlapping byte ranges: the cell law rules a load at `8` unaffected by a
store at `0`, and a byte-addressed memory does not. Distinctness of offsets is therefore
not the condition under which two spill slots are independent.

`ByteMemMachine` is the same register/frame interface with the frame indexed by a byte
offset and one access spanning `width` bytes. Its non-interference law is conditioned on
`GenericRegAlloc.SepAt width` — disjointness of the two byte ranges — so a statement
about two frame slots is provable only against an exhibited separation, which
`GenericRegAlloc.SlotsSeparated` supplies for a whole allocation and
`GenericRegAlloc.linearScan_slotsSeparated` /
`GraphColoringGeneric.selectColors_slotsSeparated` discharge from the allocator's frame
stride.

## The relationship to `MemMachine`

The two classes sit beside each other rather than one replacing the other.

* `ofMemMachine` : every `MemMachine` is a `ByteMemMachine` at any positive width. So
  restating the spill core over the byte class costs no backend — the x86
  `instMemMachineJState`, A64 `instMemMachineAMemState`, RV64 `instMemMachineRMemState`
  and vector `instMemMachineVecFrameState` instances all carry over unchanged.
* `sepAt_of_aligned` (in `GenericRegAlloc`) is the converse direction: on a
  `width`-aligned offset grid, distinctness already implies separation. A cell-indexed
  frame is the byte-addressed frame restricted to that grid, which is why the cell law is
  sound for a scalar file whose slots are the grid and unsound once a wider value is
  spilled at a narrower stride.
* `ByteFrame` is a frame of individual bytes, where an access at `off` reads the bytes
  `off, …, off + width - 1` and overlapping accesses alias. It satisfies the
  byte law (`instByteMemMachineByteFrame`) and refutes the cell law
  (`ByteFrame.cell_law_fails`), so the byte law is the strongest non-interference law
  that holds of both memory shapes.

## Instructions that touch the frame

`byteSpillStore` and `byteReload` are the two frame accesses of the spill path as state
transformers. `FrameStepMachine` is their instruction-level form: a step function on the
state, the two instructions that render a spill store and a reload, and the frame writes
and register writes of one instruction. Its two non-interference laws — a step is
invisible at every access separated from all of its frame writes, and at every register it
does not write — carry `ByteSpillValid` across a body of arbitrary instructions, so
`frameReload_sandwich` is the store/body/reload transparency over a block that computes as
well as spills. `byteReload_after_storeSeq` is the same conclusion for a body consisting
of spill stores alone.

## Main definitions

* `ByteMemMachine`: register file plus byte-addressed frame of `width`-byte accesses
* `byteSpillStore`, `byteReload`, `ByteSpillValid`: the spill store, the reload, and the
  slot-holds-the-register invariant
* `byteStoreSeq`: a sequence of spill stores — the frame traffic of a block body
* `ByteFrame`: the byte-granular frame witness
* `FrameStepMachine`: an instruction set whose steps read and write the byte-addressed
  frame, with the frame writes and register writes of one instruction
* `runFrameBlock`, `PreservesSlot`: the straight-line semantics of such an instruction set
  and the condition under which one instruction leaves a slot's contents alone

## Main results

* `byteSpillStore_establishes`, `byteReload_noop`: the single-slot roundtrip, which needs
  no separation
* `byteSpillStore_other_slot`, `byteSpillValid_store_sep`: a store leaves a separated slot
  and the invariant of a separated slot intact — the statements that carry the separation
  hypothesis
* `byteSpillValid_storeSeq`, `byteReload_after_storeSeq`: the reload after a body of spill
  stores to separated slots is a no-op
* `ByteFrame.cell_law_fails`: on a byte-granular frame, a store changes a load at a
  distinct but overlapping offset
* `byteSpillValid_step`, `byteSpillValid_runFrameBlock`, `frameReload_sandwich`: the slot
  invariant across one step, across a block, and the resulting spill/reload transparency
  over a block of frame-touching instructions
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ByteMemMachine

open CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-! ## 1. The class -/

/-- A register file plus a **byte-addressed** frame whose accesses span `width` bytes.
    The interface is `MemMachine`'s; the difference is the non-interference law, which
    holds of two accesses only when their byte ranges are disjoint (`SepAt width`). At
    `¬ SepAt width off o` the class says nothing about `load (store m off v) o`, so a
    two-slot statement cannot be proved without the separation. -/
class ByteMemMachine (M : Type) where
  /-- The register/frame value type. -/
  Val : Type
  /-- The byte width of one frame access. -/
  width : Nat
  /-- An access spans at least one byte. -/
  width_pos : 0 < width
  /-- Read a register. -/
  get : M → String → Val
  /-- Read the `width` bytes at byte offset `off`. -/
  load : M → Int → Val
  /-- Write a register. -/
  setReg : M → String → Val → M
  /-- Write the `width` bytes at byte offset `off`. -/
  store : M → Int → Val → M
  /-- Reading back a just-written access returns the stored value. -/
  load_store_same : ∀ (m : M) (off : Int) (v : Val), load (store m off v) off = v
  /-- A store leaves every **separated** access unchanged. -/
  load_store_sep : ∀ (m : M) (off o : Int) (v : Val), SepAt width off o →
    load (store m off v) o = load m o
  /-- A store leaves every register unchanged. -/
  get_store : ∀ (m : M) (off : Int) (v : Val) (r : String), get (store m off v) r = get m r
  /-- Writing register `r` a value it already holds is a no-op. -/
  setReg_get_self : ∀ (m : M) (r : String), setReg m r (get m r) = m

/-- The byte width of one frame access of `M`. -/
abbrev byteWidth (M : Type) [ByteMemMachine M] : Nat := ByteMemMachine.width (M := M)

variable {M : Type}

/-! ## 2. Every cell-indexed machine is a byte machine

`MemMachine`'s law is the byte law with the separation hypothesis dropped, so it implies
the byte law at every positive width: a `MemMachine` instance needs no re-proof to carry
the results of §3. -/

/-- **The bridge.** A cell-indexed `MemMachine` read as a byte-addressed machine of
    `w`-byte accesses: the operations are the same and the separation hypothesis is
    discharged into the cell law's `o ≠ off` by `SepAt.ne`. Not an instance — the width is
    a choice about the values the frame holds, made where the machine is used. -/
@[reducible] def ofMemMachine (M : Type) [MemMachine M] (w : Nat) (hw : 0 < w) :
    ByteMemMachine M where
  Val := MemMachine.Val M
  width := w
  width_pos := hw
  get := MemMachine.get
  load := MemMachine.load
  setReg := MemMachine.setReg
  store := MemMachine.store
  load_store_same := MemMachine.load_store_same
  load_store_sep := fun m off o v h => MemMachine.load_store_other m off o v (SepAt.ne hw h).symm
  get_store := MemMachine.get_store
  setReg_get_self := MemMachine.setReg_get_self

/-! ## 3. The spill core over the byte-addressed frame

The single-slot roundtrip (`byteSpillStore_establishes`, `byteReload_noop`) needs no
separation: it is about one slot, and `load_store_same` covers it. Separation appears
exactly where a second slot does — a store to another slot preserving this slot
(`byteSpillStore_other_slot`) and preserving its invariant
(`byteSpillValid_store_sep`), hence over a whole body of spill stores
(`byteReload_after_storeSeq`). -/

/-- The spill store: write `r`'s value to the `width` bytes at `off`. -/
def byteSpillStore [ByteMemMachine M] (m : M) (off : Int) (r : String) : M :=
  ByteMemMachine.store m off (ByteMemMachine.get m r)

/-- The reload: write the `width` bytes at `off` back into register `r`. -/
def byteReload [ByteMemMachine M] (m : M) (r : String) (off : Int) : M :=
  ByteMemMachine.setReg m r (ByteMemMachine.load m off)

/-- `ByteSpillValid off r m`: the slot at byte offset `off` holds `r`'s value in `m`. -/
def ByteSpillValid [ByteMemMachine M] (off : Int) (r : String) (m : M) : Prop :=
  ByteMemMachine.load m off = ByteMemMachine.get m r

/-- **The spill store establishes `ByteSpillValid`** for its own slot. -/
theorem byteSpillStore_establishes [ByteMemMachine M] (m : M) (off : Int) (r : String) :
    ByteSpillValid off r (byteSpillStore m off r) := by
  unfold ByteSpillValid byteSpillStore
  rw [ByteMemMachine.load_store_same, ByteMemMachine.get_store]

/-- **The reload is a no-op when the slot holds the register's value.** -/
theorem byteReload_noop [ByteMemMachine M] (m : M) (off : Int) (r : String)
    (hv : ByteSpillValid off r m) : byteReload m r off = m := by
  unfold ByteSpillValid at hv
  unfold byteReload
  rw [hv, ByteMemMachine.setReg_get_self]

/-- **A spill store leaves a separated slot unchanged.** The `MemMachine` analogue
    (`evalSpillStore_other_cell`) asks only for `o ≠ off`; here the byte ranges must be
    disjoint, which is what a `%ymm` slot pair 8 bytes apart does not satisfy. -/
theorem byteSpillStore_other_slot [ByteMemMachine M] (m : M) (off o : Int) (r : String)
    (h : SepAt (byteWidth M) off o) :
    ByteMemMachine.load (byteSpillStore m off r) o = ByteMemMachine.load m o := by
  unfold byteSpillStore
  exact ByteMemMachine.load_store_sep _ _ _ _ h

/-- **A spill store to a separated slot preserves this slot's invariant.** The frame
    write misses `off` by separation and the register file is untouched. -/
theorem byteSpillValid_store_sep [ByteMemMachine M] (m : M) (off off' : Int) (r r' : String)
    (h : SepAt (byteWidth M) off' off) (hv : ByteSpillValid off r m) :
    ByteSpillValid off r (byteSpillStore m off' r') := by
  unfold ByteSpillValid at hv ⊢
  rw [byteSpillStore_other_slot m off' off r' h]
  unfold byteSpillStore
  rw [ByteMemMachine.get_store]
  exact hv

/-- A body's frame traffic: the spill stores `(offset, register)` it performs, in order. -/
def byteStoreSeq [ByteMemMachine M] (m : M) (ss : List (Int × String)) : M :=
  ss.foldl (fun mm p => byteSpillStore mm p.1 p.2) m

/-- **The invariant survives a body of spill stores to separated slots.** -/
theorem byteSpillValid_storeSeq [ByteMemMachine M] (off : Int) (r : String) :
    ∀ (ss : List (Int × String)) (m : M), ByteSpillValid off r m →
      (∀ p ∈ ss, SepAt (byteWidth M) p.1 off) →
      ByteSpillValid off r (byteStoreSeq m ss) := by
  intro ss
  induction ss with
  | nil => intro m hv _; exact hv
  | cons p ps ih =>
    intro m hv hsep
    have hstep : ByteSpillValid off r (byteSpillStore m p.1 p.2) :=
      byteSpillValid_store_sep m off p.1 r p.2 (hsep p (List.mem_cons_self ..)) hv
    have hseq : byteStoreSeq m (p :: ps) = byteStoreSeq (byteSpillStore m p.1 p.2) ps := rfl
    rw [hseq]
    exact ih _ hstep (fun q hq => hsep q (List.mem_cons_of_mem _ hq))

/-- **The spill/reload sandwich over a byte-addressed frame.** A value stored to its slot,
    a body performing spill stores to other slots, then the reload before the value's use:
    the reload is a no-op provided every slot the body writes is separated from this one.
    The separation hypothesis is the content — dropped, the statement is false of a
    byte-addressed frame whose slots overlap. -/
theorem byteReload_after_storeSeq [ByteMemMachine M] (m : M) (off : Int) (r : String)
    (ss : List (Int × String)) (hsep : ∀ p ∈ ss, SepAt (byteWidth M) p.1 off) :
    byteReload (byteStoreSeq (byteSpillStore m off r) ss) r off
      = byteStoreSeq (byteSpillStore m off r) ss :=
  byteReload_noop _ off r
    (byteSpillValid_storeSeq off r ss _ (byteSpillStore_establishes m off r) hsep)

/-- **The separation hypotheses of a body are read off a separated allocation.** Every
    slot of a `SlotsSeparated width` allocation other than `off` is separated from `off`,
    so the sandwich's hypothesis follows from the allocator-level obligation. -/
theorem sepAt_of_slotsSeparated {width : Nat} {decisions : List (String × Slot)}
    (h : SlotsSeparated width decisions) {off o : Int} (hoff : off ∈ slotOffsets decisions)
    (ho : o ∈ slotOffsets decisions) (hne : o ≠ off) : SepAt width o off :=
  sepAt_of_pairwise_mem h ho hoff hne

/-! ## 4. A byte-granular frame: the class is not only satisfied by cell models

`ByteFrame n` holds one byte per address; an `n`-byte access at `off` covers the addresses
`off, …, off + n - 1`. Overlapping accesses alias, so the cell law is refutable there
(`cell_law_fails`) while the byte law holds (`instByteMemMachineByteFrame`). -/

/-- A frame of individual bytes, with a register file of `n`-byte values. -/
structure ByteFrame (n : Nat) where
  /-- The register file. -/
  regs : String → (Fin n → BitVec 8)
  /-- The frame, one byte per address. -/
  bytes : Int → BitVec 8

namespace ByteFrame

variable {n : Nat}

/-- Read the `n` bytes at `off`. -/
def loadB (m : ByteFrame n) (off : Int) : Fin n → BitVec 8 :=
  fun i => m.bytes (off + (i.val : Int))

/-- Write the `n` bytes at `off`. -/
def storeB (m : ByteFrame n) (off : Int) (v : Fin n → BitVec 8) : ByteFrame n :=
  { m with bytes := fun o =>
      if h : off ≤ o ∧ o < off + (n : Int) then v ⟨(o - off).toNat, by omega⟩ else m.bytes o }

/-- Write a register. -/
def setRegB (m : ByteFrame n) (r : String) (v : Fin n → BitVec 8) : ByteFrame n :=
  { m with regs := fun x => if x = r then v else m.regs x }

/-- Reading back a just-written access returns the stored value. -/
theorem loadB_storeB_same (m : ByteFrame n) (off : Int) (v : Fin n → BitVec 8) :
    loadB (storeB m off v) off = v := by
  funext i
  have hi : (i.val : Int) < (n : Int) := by exact_mod_cast i.isLt
  have hidx : (off + (i.val : Int) - off).toNat = i.val := by omega
  simp only [loadB, storeB]
  rw [dite_eq_left (by omega : off ≤ off + (i.val : Int) ∧ off + (i.val : Int) < off + (n : Int))]
  simp only [hidx]

/-- A store leaves a separated access unchanged: every byte the load reads lies outside
    the byte range the store wrote. -/
theorem loadB_storeB_sep (m : ByteFrame n) (off o : Int) (v : Fin n → BitVec 8)
    (h : SepAt n off o) : loadB (storeB m off v) o = loadB m o := by
  funext i
  have hi : (i.val : Int) < (n : Int) := by exact_mod_cast i.isLt
  have hi0 : (0 : Int) ≤ (i.val : Int) := Int.natCast_nonneg _
  simp only [loadB, storeB]
  rw [dite_eq_right (by rcases h with h | h <;> omega)]

/-- A store leaves the register file unchanged. -/
theorem regs_storeB (m : ByteFrame n) (off : Int) (v : Fin n → BitVec 8) (r : String) :
    (storeB m off v).regs r = m.regs r := rfl

/-- A register write leaves the frame unchanged. -/
theorem loadB_setRegB (m : ByteFrame n) (r : String) (v : Fin n → BitVec 8) (o : Int) :
    loadB (setRegB m r v) o = loadB m o := rfl

/-- Writing one register leaves the others unchanged. -/
theorem regs_setRegB_other (m : ByteFrame n) (r x : String) (v : Fin n → BitVec 8)
    (h : x ≠ r) : (setRegB m r v).regs x = m.regs x := ite_eq_right h

/-- Writing a register a value it already holds is a no-op. -/
theorem setRegB_regs_self (m : ByteFrame n) (r : String) : setRegB m r (m.regs r) = m := by
  cases m with
  | mk regs bytes =>
    simp only [setRegB, ByteFrame.mk.injEq, and_true]
    funext x
    by_cases h : x = r <;> simp [h]

/-- **The cell law is refutable on a byte-granular frame.** The `4`-byte accesses at `0`
    and `2` have distinct offsets and overlapping byte ranges, and the store at `0` changes
    the load at `2`. So `MemMachine.load_store_other` — non-interference from `o ≠ off`
    alone — has no instance here, and the class law of `ByteMemMachine` is the strongest
    one that holds of both this frame and a cell-indexed one. -/
theorem cell_law_fails :
    ∃ (m : ByteFrame 4) (off o : Int) (v : Fin 4 → BitVec 8),
      o ≠ off ∧ loadB (storeB m off v) o ≠ loadB m o := by
  refine ⟨⟨fun _ _ => 0, fun _ => 0⟩, 0, 2, fun _ => 1, by decide, ?_⟩
  intro hEq
  have h0 := congrFun hEq (0 : Fin 4)
  simp only [loadB, storeB] at h0
  simp at h0

end ByteFrame

/-- **The byte-granular frame is a `ByteMemMachine`** of `n+1`-byte accesses. -/
instance instByteMemMachineByteFrame (n : Nat) : ByteMemMachine (ByteFrame (n + 1)) where
  Val := Fin (n + 1) → BitVec 8
  width := n + 1
  width_pos := Nat.succ_pos n
  get m r := m.regs r
  load := ByteFrame.loadB
  setReg := ByteFrame.setRegB
  store := ByteFrame.storeB
  load_store_same := ByteFrame.loadB_storeB_same
  load_store_sep := fun m off o v h => ByteFrame.loadB_storeB_sep m off o v h
  get_store := ByteFrame.regs_storeB
  setReg_get_self := ByteFrame.setRegB_regs_self

/-- The `4`-byte frame's access width is `4`, so `SepAt 4` is the separation its
    non-interference law asks for. -/
theorem byteWidth_byteFrame_four : byteWidth (ByteFrame 4) = 4 := rfl

/-- The offsets `0` and `2` are not separated at width `4` — the overlap
    `ByteFrame.cell_law_fails` exhibits, as a decidable fact about the offsets alone. -/
theorem not_sepAt_four_zero_two : ¬ SepAt 4 0 2 := by decide

/-! ## 5. Instructions that touch the frame

§3 is about the two frame accesses as state transformers, so a body between a spill store
and its reload can only be a further sequence of spill stores (`byteStoreSeq`).
`FrameStepMachine` adds the instruction level: a step function, the spill-store and reload
instructions, and the frame writes and register writes each instruction performs. The
class's two non-interference laws say a step is invisible at every access separated from
its frame writes and at every register it does not write, which is what carries
`ByteSpillValid` across a body whose instructions also compute. -/

/-- **An instruction set over a byte-addressed frame.** The state is a `ByteMemMachine`;
    `step` is one instruction's effect; `mkFrameStore` / `mkFrameLoad` are the instructions
    that render a spill store and a reload; `frameWrites` and `regWrites` are the frame
    slots and registers one instruction writes. The two laws bound a step's effect by those
    two lists: a step changes no access separated from all of its frame writes, and no
    register outside `regWrites`. A step whose frame write overlaps a slot is unconstrained
    by them, so a statement about a slot across such a body is provable only against an
    exhibited separation. -/
class FrameStepMachine (I : Type) (M : Type) extends ByteMemMachine M where
  /-- One instruction's effect on the state. -/
  step : M → I → M
  /-- The instruction that spills register `r` to the frame slot at byte offset `off`. -/
  mkFrameStore : Int → String → I
  /-- The instruction that reloads the frame slot at byte offset `off` into register `r`. -/
  mkFrameLoad : String → Int → I
  /-- The `(byte offset, source register)` frame writes of an instruction. -/
  frameWrites : I → List (Int × String)
  /-- The register names an instruction writes. -/
  regWrites : I → List String
  /-- The spill-store instruction writes the register's value at its offset. -/
  step_mkFrameStore : ∀ (m : M) (off : Int) (r : String),
    step m (mkFrameStore off r) = byteSpillStore m off r
  /-- The reload instruction writes the slot's contents into the register. -/
  step_mkFrameLoad : ∀ (m : M) (r : String) (off : Int),
    step m (mkFrameLoad r off) = byteReload m r off
  /-- A step leaves every access separated from all of its frame writes unchanged. -/
  load_step_sep : ∀ (m : M) (i : I) (o : Int),
    (∀ p ∈ frameWrites i, SepAt (ByteMemMachine.width (M := M)) p.1 o) →
    ByteMemMachine.load (step m i) o = ByteMemMachine.load m o
  /-- A step leaves every register it does not write unchanged. -/
  get_step_other : ∀ (m : M) (i : I) (r : String),
    r ∉ regWrites i → ByteMemMachine.get (step m i) r = ByteMemMachine.get m r

variable {I : Type}

/-- Straight-line block semantics: the left fold of the step. -/
def runFrameBlock [FrameStepMachine I M] (m : M) (block : List I) : M :=
  block.foldl (fun (mm : M) (i : I) => FrameStepMachine.step mm i) m

/-- The empty block is a no-op. -/
@[simp] theorem runFrameBlock_nil [FrameStepMachine I M] (m : M) :
    runFrameBlock (I := I) m [] = m := rfl

/-- One step, then the rest of the block. -/
theorem runFrameBlock_cons [FrameStepMachine I M] (m : M) (i : I) (rest : List I) :
    runFrameBlock m (i :: rest) = runFrameBlock (FrameStepMachine.step m i) rest := rfl

/-- `runFrameBlock` distributes over `++`. -/
theorem runFrameBlock_append [FrameStepMachine I M] (m : M) (xs ys : List I) :
    runFrameBlock m (xs ++ ys) = runFrameBlock (runFrameBlock m xs) ys := by
  simp [runFrameBlock, List.foldl_append]

/-- `PreservesSlot M off r i`: the instruction `i` writes no frame slot overlapping the
    `width` bytes at `off` and does not write register `r`. These are the two ways a step
    can invalidate `ByteSpillValid off r`, and the frame half is byte separation rather
    than offset distinctness. -/
def PreservesSlot (M : Type) [FrameStepMachine I M] (off : Int) (r : String) (i : I) : Prop :=
  (∀ p ∈ FrameStepMachine.frameWrites M i, SepAt (byteWidth M) p.1 off)
    ∧ r ∉ FrameStepMachine.regWrites M i

/-- **A slot-preserving step preserves the slot's invariant.** The frame write misses the
    slot by separation and the register keeps its value. -/
theorem byteSpillValid_step [FrameStepMachine I M] {off : Int} {r : String} {m : M} {i : I}
    (hi : PreservesSlot M off r i) (hv : ByteSpillValid off r m) :
    ByteSpillValid off r (FrameStepMachine.step m i) := by
  unfold ByteSpillValid at hv ⊢
  rw [FrameStepMachine.load_step_sep m i off hi.1, hv,
    FrameStepMachine.get_step_other m i r hi.2]

/-- **The invariant survives a block of slot-preserving steps.** -/
theorem byteSpillValid_runFrameBlock [FrameStepMachine I M] (off : Int) (r : String) :
    ∀ (block : List I) (m : M), ByteSpillValid off r m →
      (∀ i ∈ block, PreservesSlot M off r i) →
      ByteSpillValid off r (runFrameBlock m block) := by
  intro block
  induction block with
  | nil => intro m hv _; exact hv
  | cons i is ih =>
    intro m hv hpres
    rw [runFrameBlock_cons]
    exact ih _ (byteSpillValid_step (hpres i (List.mem_cons_self ..)) hv)
      (fun j hj => hpres j (List.mem_cons_of_mem _ hj))

/-- **The spill/reload sandwich over a block of frame-touching instructions.** A value
    stored to the slot at byte offset `off`, a body whose frame writes are all separated
    from that slot and which does not write `r`, then the reload before `r`'s use: the
    reload does not change the block's final state. The separation half of the hypothesis
    is the content — a body writing a slot whose byte range meets `[off, off + width)`
    changes what the reload reads. -/
theorem frameReload_sandwich [FrameStepMachine I M] (m : M) (off : Int) (r : String)
    (mid rest : List I) (hpres : ∀ i ∈ mid, PreservesSlot M off r i) :
    runFrameBlock m (FrameStepMachine.mkFrameStore M off r ::
        (mid ++ FrameStepMachine.mkFrameLoad M r off :: rest))
      = runFrameBlock m (FrameStepMachine.mkFrameStore M off r :: (mid ++ rest)) := by
  have hv0 : ByteSpillValid off r
      (FrameStepMachine.step m (FrameStepMachine.mkFrameStore (I := I) M off r)) := by
    rw [FrameStepMachine.step_mkFrameStore]
    exact byteSpillStore_establishes m off r
  have hv1 := byteSpillValid_runFrameBlock (I := I) off r mid _ hv0 hpres
  rw [runFrameBlock_cons, runFrameBlock_cons, runFrameBlock_append, runFrameBlock_append,
    runFrameBlock_cons, FrameStepMachine.step_mkFrameLoad, byteReload_noop _ off r hv1]

end CatCrypt.Crypto.Optimizer.ByteMemMachine
