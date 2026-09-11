/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-!
# Source→machine constant-time bridge, Phase 2: the MEMORY/ARRAY fragment

`LowCTToJInstrCT.lean` (Phase 1) bridged the **memory-free** scalar-arith
fragment.  There the source CT verdict (`cmdCT`) was *not* load-bearing for
machine CT: the lowering emitted only register `mov`/ALU ops, which are always
`IsDirect`, so the leaf was constant-time **unconditionally** — the `cmdCT`
hypothesis was carried for contract shape only.

This module builds the fragment where the source analysis genuinely *drives*
machine constant-time: **array element load/store** (`arr[idx] := src`,
`dst := arr[idx]`).  These lower to the register-INDEXED machine ops
`storeMemIdx`/`loadMemIdx`, whose effective address reads the **value** in the
index register.  Such an instruction is constant-time **iff** its index
register is in the public address frame (`pub idx = true`).  An indexed access
with a secret index leaks the index value into the cache-line trace
(`MachineConstantTime.nonCT_storeMemIdx_leaks_value`).

So here the source-side guarantee is essential: the source CT analyser forces
the index slot `.Public` (`cmdCT` arm for `RArrStore`/`RArrLoad`,
`LowCTCTAnalysis.lean` §214–219), and — provided the register allocator places
public slots in frame registers (`FrameWF`) — that supplies the
`pub (ρ idx) = true` premise the machine keystone
(`MachineConstantTime.blockLeak_pub_determined`) needs.  `cmdCT` does real work.

## The source signatures this bridges (quoted from the real `LowCT`)

`LowCT.lean`:
```
  | RArrStore  : (arr : Located) → (idxVar : String) → (src : Located) → LowCT
  | RArrLoad   : (dst : Located) → (src : Located) → (idxVar : String) → LowCT
```
`LowCTCTAnalysis.lean` `cmdCT` arms (§214–219) / reduction lemmas (§359–369):
```
  | .RArrStore arr idxVar src =>
      lt idxVar == .Public && lt arr.locVar == .Public && lt src.locVar == .Public
  | .RArrLoad  dst src idxVar =>
      lt idxVar == .Public && lt dst.locVar == .Public && lt src.locVar == .Public
```
The index slot is forced `.Public` in **both** arms — exactly the
public-index guarantee that drives the machine keystone.

The machine indexed ops (`JasminModel.lean` §640/§644):
```
  | loadMemIdx  (dst base idx : String) (scale : Nat)
  | storeMemIdx (base idx : String) (scale : Nat) (src : JOperand)
```
with `dstRegs (.storeMemIdx ..) = []`, `dstRegs (.loadMemIdx d ..) = [d]`,
`idxReg (.loadMemIdx _ _ idx _) = some idx`,
`idxReg (.storeMemIdx _ idx _ _) = some idx`
(`MachineConstantTime`).

## What is proved (the CT half)

* `MemSrc` / `MemSrc.toLowCT` — the array store/load fragment as a faithful
  subset of `LowCT`, embedded into the **real** `RArrStore`/`RArrLoad` node, so
  the source CT verdict analysed is the genuine `cmdCT`.
* `lowerMemStore_CTAddressed` / `lowerMemLoad_CTAddressed` — each lowering is
  `CTAddressed` w.r.t. `pub`, **given** `pub (ρ idx) = true` (and, for the load,
  the result-register-is-data convention `pub (ρ dst) = false`).  For the store
  this reduces to the index premise alone (`dstRegs = []` — the second conjunct
  is vacuous).
* block versions over `List MemSrc` + `lowerMemSeq_constant_time` via the
  machine keystone `blockLeak_pub_determined` under `agreePub`.
* `FrameWF` + `cmdCT_supplies_storeIdx_pub` / `cmdCT_supplies_loadIdx_pub` —
  **the characteristic Phase-2 tie**: the source `cmdCT = true` verdict, routed
  through a frame-consistent register map, supplies the `pub (ρ idx) = true`
  premise.  This is where `cmdCT` is genuinely consumed for machine CT.
* `lowerMem_source_to_machine_CT` (single) and `lowerMemSeq_source_to_machine_CT`
  (block) — end-to-end: `cmdCT = true → FrameWF → agreePub → blockLeak s₁ … =
  blockLeak s₂ …`.

## Scope notes

* The **load** result-register convention `pub (ρ dst) = false` is a
  register-allocation discipline assumption (results go in data registers, not
  the address frame), stated as a hypothesis — *not* derived.  A real allocator
  guarantees it; we record it as the WF side condition.
* **OUT OF SCOPE — the denotation half.**  This module proves nothing about the
  *value* the load/store computes through the source array oracle
  (`LeafSpec.arrStore`/`arrLoad`, which is parametric/identity by default).
  Closing that requires pinning `leafSpec` to a concrete byte-offset memory
  model and an array↦(base, scale) memory correspondence, mirroring
  `lowerArith_denote` for the scalar fragment.  That is the next step; here we
  deliver the CT half only (the genuine "source public-index analysis ⇒ machine
  CT" content, which the memory-free fragment did not need).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. The array memory-access source fragment (a faithful `LowCT` subset) -/

/-- A source array **store** `arr[idx] := src` with element `scale` (the byte
    stride of one element, used to form the machine effective address).  A
    faithful subset of `LowCT.RArrStore`: `arr` is the array base slot, `idx`
    the runtime index slot, `src` the value slot.  `arrTy`/`srcTy` carry the
    `TowerType`s the `Located` nodes need for the embedding. -/
structure MemStoreSrc where
  arr   : String
  idx   : String
  src   : String
  scale : Nat
  arrTy : TowerType
  srcTy : TowerType
  deriving Repr

/-- A source array **load** `dst := arr[idx]` with element `scale`.  A faithful
    subset of `LowCT.RArrLoad`. -/
structure MemLoadSrc where
  dst   : String
  arr   : String
  idx   : String
  scale : Nat
  dstTy : TowerType
  arrTy : TowerType
  deriving Repr

/-! ## 2. Embedding into real `LowCT` -/

/-- **The store embedding into real `LowCT`.**  A `MemStoreSrc` is the genuine
    `LowCT` command `RArrStore ⟨arr⟩ idx ⟨src⟩`, so the source CT verdict
    analysed is the real `cmdCT`. -/
def MemStoreSrc.toLowCT (m : MemStoreSrc) : LowCT :=
  .RArrStore ⟨m.arr, m.arrTy⟩ m.idx ⟨m.src, m.srcTy⟩

/-- **The load embedding into real `LowCT`.**  A `MemLoadSrc` is the genuine
    `LowCT` command `RArrLoad ⟨dst⟩ ⟨arr⟩ idx`. -/
def MemLoadSrc.toLowCT (m : MemLoadSrc) : LowCT :=
  .RArrLoad ⟨m.dst, m.dstTy⟩ ⟨m.arr, m.arrTy⟩ m.idx

/-- The store source CT verdict, via the **real** `cmdCT`: `true` iff the index,
    array, and source slots are all `Public`.  (The index-slot being forced
    `Public` is the public-index guarantee Phase 2 consumes.) -/
theorem MemStoreSrc.cmdCT_iff (m : MemStoreSrc) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT m.toLowCT lt leafCT = true ↔
      (lt m.idx == .Public) ∧ (lt m.arr == .Public) ∧ (lt m.src == .Public) := by
  simp [MemStoreSrc.toLowCT, cmdCT_RArrStore, Bool.and_eq_true, and_assoc]

/-- The load source CT verdict, via the **real** `cmdCT`: `true` iff the index,
    destination, and array slots are all `Public`. -/
theorem MemLoadSrc.cmdCT_iff (m : MemLoadSrc) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT m.toLowCT lt leafCT = true ↔
      (lt m.idx == .Public) ∧ (lt m.dst == .Public) ∧ (lt m.arr == .Public) := by
  simp [MemLoadSrc.toLowCT, cmdCT_RArrLoad, Bool.and_eq_true, and_assoc]

/-! ## 3. The lowering to the register-indexed machine ops -/

/-- **The store lowering.**  `arr[idx] := src` lowers to a single register-indexed
    scatter `mov %src, (%arr,%idx,scale)` — `storeMemIdx`, whose effective offset
    is `scale · (value in ρ idx)`.  This is the op the memory-free fragment never
    emitted: it reads the index register's value, so its CT status hinges on
    `ρ idx` being a public frame register. -/
def lowerMemStore (ρ : RegMap) (m : MemStoreSrc) : JInstr 64 :=
  .storeMemIdx (ρ m.arr) (ρ m.idx) m.scale (.reg (ρ m.src))

/-- **The load lowering.**  `dst := arr[idx]` lowers to a register-indexed gather
    `mov (%arr,%idx,scale), %dst` — `loadMemIdx`, writing `ρ dst` and reading
    `ρ idx` for the address. -/
def lowerMemLoad (ρ : RegMap) (m : MemLoadSrc) : JInstr 64 :=
  .loadMemIdx (ρ m.dst) (ρ m.arr) (ρ m.idx) m.scale

/-! ## 4. The CT half: each lowering is `CTAddressed`, given the index premise -/

/-- **Store is `CTAddressed` from the index premise alone.**  A `storeMemIdx`
    writes no register (`dstRegs (.storeMemIdx ..) = []`), so `CTAddressed`'s
    second conjunct is **vacuous**; the whole condition reduces to
    `pub (ρ idx) = true` for the single index register `idxReg = some (ρ idx)`.
    This `pub (ρ idx) = true` premise is exactly what the source `cmdCT` verdict
    supplies (via `FrameWF`, §6) — for the store, nothing else is required. -/
theorem lowerMemStore_CTAddressed (pub : PubPred) (ρ : RegMap) (m : MemStoreSrc)
    (hidx : pub (ρ m.idx) = true) :
    CTAddressed pub (lowerMemStore ρ m) := by
  refine ⟨?_, ?_⟩
  · intro idx h
    -- `idxReg (storeMemIdx ..) = some (ρ m.idx)`, so `idx = ρ m.idx`.
    simp only [lowerMemStore, idxReg, Option.some.injEq] at h
    subst h; exact hidx
  · -- `dstRegs (storeMemIdx ..) = []` — the destination obligation is vacuous.
    intro d hd; simp only [lowerMemStore, dstRegs, List.not_mem_nil] at hd

/-- **Load is `CTAddressed` from the index premise plus the result-data
    convention.**  A `loadMemIdx d ..` writes its destination register `d`
    (`dstRegs = [d]`), so `CTAddressed` additionally requires `pub (ρ dst) =
    false`: the loaded value lands in a *data* register, not the public address
    frame.  That is a register-allocation discipline assumption (results go in
    data registers); we state it as the hypothesis `hdst`, not derive it. -/
theorem lowerMemLoad_CTAddressed (pub : PubPred) (ρ : RegMap) (m : MemLoadSrc)
    (hidx : pub (ρ m.idx) = true) (hdst : pub (ρ m.dst) = false) :
    CTAddressed pub (lowerMemLoad ρ m) := by
  refine ⟨?_, ?_⟩
  · intro idx h
    simp only [lowerMemLoad, idxReg, Option.some.injEq] at h
    subst h; exact hidx
  · intro d hd
    simp only [lowerMemLoad, dstRegs, List.mem_singleton] at hd
    subst hd; exact hdst

/-! ## 5. Block versions and machine constant-time

A leaf is a sequence of array ops.  We allow a heterogeneous sequence by
tagging each statement as a store or a load.  `lowerMemSeq` lowers the block;
`memSeqCTAddressed` is the per-statement `CTAddressed` hypothesis; the keystone
`blockLeak_pub_determined` then gives machine CT under `agreePub`. -/

/-- A single array statement: a store or a load. -/
inductive MemSrc where
  | store (m : MemStoreSrc)
  | load  (m : MemLoadSrc)
  deriving Repr

/-- The `LowCT` embedding of one statement. -/
def MemSrc.toLowCT : MemSrc → LowCT
  | .store m => m.toLowCT
  | .load  m => m.toLowCT

/-- The lowering of one statement to its register-indexed machine op. -/
def lowerMem (ρ : RegMap) : MemSrc → JInstr 64
  | .store m => lowerMemStore ρ m
  | .load  m => lowerMemLoad ρ m

/-- **The block lowering.**  A list of array statements lowers to the list of the
    per-statement register-indexed ops. -/
def lowerMemSeq (ρ : RegMap) (ms : List MemSrc) : List (JInstr 64) :=
  ms.map (lowerMem ρ)

@[simp] theorem lowerMemSeq_nil (ρ : RegMap) : lowerMemSeq ρ [] = [] := rfl

@[simp] theorem lowerMemSeq_cons (ρ : RegMap) (m : MemSrc) (ms : List MemSrc) :
    lowerMemSeq ρ (m :: ms) = lowerMem ρ m :: lowerMemSeq ρ ms := rfl

/-- The per-statement CT premise: the index register is public, and (for a load)
    the result register is a data register.  This is the `CTAddressed`-supplying
    side condition for one statement. -/
def MemSrc.ctPremise (pub : PubPred) (ρ : RegMap) : MemSrc → Prop
  | .store m => pub (ρ m.idx) = true
  | .load  m => pub (ρ m.idx) = true ∧ pub (ρ m.dst) = false

/-- Each statement satisfying its CT premise lowers to a `CTAddressed` machine op. -/
theorem lowerMem_CTAddressed (pub : PubPred) (ρ : RegMap) (m : MemSrc)
    (h : m.ctPremise pub ρ) : CTAddressed pub (lowerMem ρ m) := by
  cases m with
  | store m => exact lowerMemStore_CTAddressed pub ρ m h
  | load  m => exact lowerMemLoad_CTAddressed pub ρ m h.1 h.2

/-- Whole block: every lowered instruction is `CTAddressed`, from the
    per-statement CT premises. -/
theorem lowerMemSeq_CTAddressed (pub : PubPred) (ρ : RegMap) (ms : List MemSrc)
    (h : ∀ m ∈ ms, m.ctPremise pub ρ) :
    ∀ i ∈ lowerMemSeq ρ ms, CTAddressed pub i := by
  intro i hi
  simp only [lowerMemSeq, List.mem_map] at hi
  obtain ⟨m, hm, rfl⟩ := hi
  exact lowerMem_CTAddressed pub ρ m (h m hm)

/-- **Machine constant-time, block-level (the genuine half).**  A lowered array
    leaf whose every index register is public (and every load result is a data
    register) produces the **same** machine leakage trace from any two states
    that **agree on the public registers** — even if they differ arbitrarily on
    the secret data.  Delivered by the machine keystone
    `blockLeak_pub_determined`.  Unlike the memory-free fragment this is *not*
    unconditional: it requires the public-index premises (`storeMemIdx`/
    `loadMemIdx` are `¬ IsDirect`; a secret index would leak — cf.
    `nonCT_storeMemIdx_leaks_value`). -/
theorem lowerMemSeq_constant_time (pub : PubPred) (ρ : RegMap) (ms : List MemSrc)
    (h : ∀ m ∈ ms, m.ctPremise pub ρ) (s₁ s₂ : JState 64)
    (hag : agreePub pub s₁ s₂) :
    blockLeak s₁ (lowerMemSeq ρ ms) = blockLeak s₂ (lowerMemSeq ρ ms) :=
  blockLeak_pub_determined pub (lowerMemSeq ρ ms)
    (lowerMemSeq_CTAddressed pub ρ ms h) s₁ s₂ hag

/-! ## 6. The characteristic Phase-2 tie: source `cmdCT` supplies the index premise

A register map is **frame-consistent** when every source slot the analyser
typed `.Public` is placed in a public (frame) machine register.  Under that
condition the source CT verdict `cmdCT = true` — which forces the index slot
`.Public` — supplies the `pub (ρ idx) = true` premise the machine keystone
needs.  This is where `cmdCT` does real work for machine CT: the memory-free
fragment never used it, the array fragment cannot do without it. -/

/-- **Frame well-formedness of a register map.**  Every source slot typed
    `.Public` by the analyser is mapped to a public (frame) machine register.
    A real register allocator that keeps public addresses/indices/counters in a
    designated frame satisfies this. -/
def FrameWF (lt : LevelTable) (ρ : RegMap) (pub : PubPred) : Prop :=
  ∀ v, lt v = .Public → pub (ρ v) = true

/-- **`cmdCT` supplies the store index premise.**  If the source store passes
    `cmdCT`, its index slot is `.Public`; a frame-consistent `ρ` then maps it to
    a public register, giving `pub (ρ idx) = true`. -/
theorem cmdCT_supplies_storeIdx_pub (lt : LevelTable) (leafCT : LeafCTTable)
    (ρ : RegMap) (pub : PubPred) (m : MemStoreSrc)
    (hsrc : cmdCT m.toLowCT lt leafCT = true) (hframe : FrameWF lt ρ pub) :
    pub (ρ m.idx) = true := by
  rw [MemStoreSrc.cmdCT_iff] at hsrc
  exact hframe m.idx (level_beq_public_iff.mp hsrc.1)

/-- **`cmdCT` supplies the load index premise.**  Symmetric to the store case. -/
theorem cmdCT_supplies_loadIdx_pub (lt : LevelTable) (leafCT : LeafCTTable)
    (ρ : RegMap) (pub : PubPred) (m : MemLoadSrc)
    (hsrc : cmdCT m.toLowCT lt leafCT = true) (hframe : FrameWF lt ρ pub) :
    pub (ρ m.idx) = true := by
  rw [MemLoadSrc.cmdCT_iff] at hsrc
  exact hframe m.idx (level_beq_public_iff.mp hsrc.1)

/-- **Single-statement source CT ⇒ machine CT.**  For a store, the source
    `cmdCT` verdict through a frame-consistent `ρ` is *sufficient* for machine
    constant-time: it supplies the public-index premise, and the store writes no
    register.  This is the genuine source-analysis ⇒ machine-CT tie — `cmdCT` is
    consumed, not carried. -/
theorem lowerMemStore_source_to_machine_CT (lt : LevelTable) (leafCT : LeafCTTable)
    (ρ : RegMap) (pub : PubPred) (m : MemStoreSrc)
    (hsrc : cmdCT m.toLowCT lt leafCT = true) (hframe : FrameWF lt ρ pub)
    (s₁ s₂ : JState 64) (hag : agreePub pub s₁ s₂) :
    blockLeak s₁ [lowerMemStore ρ m] = blockLeak s₂ [lowerMemStore ρ m] := by
  have hidx := cmdCT_supplies_storeIdx_pub lt leafCT ρ pub m hsrc hframe
  refine blockLeak_pub_determined pub [lowerMemStore ρ m] ?_ s₁ s₂ hag
  intro i hi
  rw [List.mem_singleton] at hi; subst hi
  exact lowerMemStore_CTAddressed pub ρ m hidx

/-- **Single-statement source CT ⇒ machine CT, load.**  For a load the source
    `cmdCT` supplies the public-index premise; the result-data convention
    `pub (ρ dst) = false` is the additional RegAlloc-discipline hypothesis
    (results go in data registers, not the address frame). -/
theorem lowerMemLoad_source_to_machine_CT (lt : LevelTable) (leafCT : LeafCTTable)
    (ρ : RegMap) (pub : PubPred) (m : MemLoadSrc)
    (hsrc : cmdCT m.toLowCT lt leafCT = true) (hframe : FrameWF lt ρ pub)
    (hdst : pub (ρ m.dst) = false)
    (s₁ s₂ : JState 64) (hag : agreePub pub s₁ s₂) :
    blockLeak s₁ [lowerMemLoad ρ m] = blockLeak s₂ [lowerMemLoad ρ m] := by
  have hidx := cmdCT_supplies_loadIdx_pub lt leafCT ρ pub m hsrc hframe
  refine blockLeak_pub_determined pub [lowerMemLoad ρ m] ?_ s₁ s₂ hag
  intro i hi
  rw [List.mem_singleton] at hi; subst hi
  exact lowerMemLoad_CTAddressed pub ρ m hidx hdst

/-! ### Block-level end-to-end tie

The block CT premise is supplied by `cmdCT = true` on each statement under a
frame-consistent `ρ`, modulo the per-load result-data convention which remains a
RegAlloc-discipline side condition (collected in `loadResultsAreData`). -/

/-- The RegAlloc-discipline side condition for a block: every load result is a
    data register.  Real allocators guarantee this; it is the part the source CT
    analyser (which classifies slots, not registers) cannot supply. -/
def loadResultsAreData (pub : PubPred) (ρ : RegMap) : List MemSrc → Prop
  | [] => True
  | .store _ :: ms => loadResultsAreData pub ρ ms
  | .load m :: ms => pub (ρ m.dst) = false ∧ loadResultsAreData pub ρ ms

/-- `loadResultsAreData` gives the result-data side condition for each load in
    the block. -/
theorem loadResultsAreData_mem (pub : PubPred) (ρ : RegMap) :
    ∀ (ms : List MemSrc), loadResultsAreData pub ρ ms →
      ∀ m ∈ ms, ∀ md : MemLoadSrc, m = .load md → pub (ρ md.dst) = false
  | [], _, m, hm => by simp at hm
  | m' :: ms, hdata, m, hm => by
      rcases List.mem_cons.mp hm with rfl | hm'
      · cases m with
        | store _ => intro md hmd; cases hmd
        | load _ => intro md hmd; cases hmd; exact hdata.1
      · cases m' with
        | store _ => exact loadResultsAreData_mem pub ρ ms hdata m hm'
        | load _ => exact loadResultsAreData_mem pub ρ ms hdata.2 m hm'

/-- The source CT verdict on a statement supplies its `ctPremise`, given a
    frame-consistent `ρ` and (for loads) the result-data side condition. -/
theorem cmdCT_supplies_ctPremise (lt : LevelTable) (leafCT : LeafCTTable)
    (ρ : RegMap) (pub : PubPred) (m : MemSrc)
    (hsrc : cmdCT m.toLowCT lt leafCT = true) (hframe : FrameWF lt ρ pub)
    (hdata : ∀ md : MemLoadSrc, m = .load md → pub (ρ md.dst) = false) :
    m.ctPremise pub ρ := by
  cases m with
  | store m => exact cmdCT_supplies_storeIdx_pub lt leafCT ρ pub m hsrc hframe
  | load m =>
      exact ⟨cmdCT_supplies_loadIdx_pub lt leafCT ρ pub m hsrc hframe, hdata m rfl⟩

/-- **Block-level source CT ⇒ machine CT (end to end).**  If every statement of
    the array leaf passes the source `cmdCT`, the register map is
    frame-consistent, and load results are data registers, then the lowered leaf
    is constant-time: any two states agreeing on the public registers produce the
    same machine leakage trace — even differing arbitrarily on the secret data.

    This is the genuine Phase-2 result: the source public-index analysis
    (`cmdCT` forcing each index `.Public`), routed through the frame-consistent
    register map, is what makes the register-indexed machine accesses
    constant-time.  `cmdCT` is load-bearing — a secret index would lower to a
    leaking `storeMemIdx`/`loadMemIdx` (cf. `nonCT_storeMemIdx_leaks_value`). -/
theorem lowerMemSeq_source_to_machine_CT (lt : LevelTable) (leafCT : LeafCTTable)
    (ρ : RegMap) (pub : PubPred) (ms : List MemSrc)
    (hsrc : ∀ m ∈ ms, cmdCT m.toLowCT lt leafCT = true) (hframe : FrameWF lt ρ pub)
    (hdata : loadResultsAreData pub ρ ms)
    (s₁ s₂ : JState 64) (hag : agreePub pub s₁ s₂) :
    blockLeak s₁ (lowerMemSeq ρ ms) = blockLeak s₂ (lowerMemSeq ρ ms) := by
  refine lowerMemSeq_constant_time pub ρ ms ?_ s₁ s₂ hag
  intro m hm
  exact cmdCT_supplies_ctPremise lt leafCT ρ pub m (hsrc m hm) hframe
    (loadResultsAreData_mem pub ρ ms hdata m hm)

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemCT
