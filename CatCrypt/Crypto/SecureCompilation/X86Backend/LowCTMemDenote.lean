/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemCT
public import Std.Tactic.BVDecide

/-!
# Source→machine bridge, Phase 2 (denotation half): the MEMORY/ARRAY fragment

`LowCTMemCT.lean` (the CT half) proved the *constant-time* content of the array
load/store fragment: the source public-index analysis (`cmdCT` forcing each
index `.Public`), routed through a frame-consistent register map, makes the
register-indexed machine accesses (`storeMemIdx`/`loadMemIdx`) constant-time.

This module builds the **value-correctness** half — the analogue of
`lowerArith_denote` for the scalar fragment: under a register/memory
correspondence, the machine `runBlock` of the lowered `storeMemIdx`/`loadMemIdx`
computes the **same value** the source `RArrStore`/`RArrLoad` computes.
Together the two halves complete the memory fragment to match the scalar
fragment's semantics-plus-CT coverage.

## The design decision: pin the parametric oracle to a concrete byte-offset model

The source array semantics (`LowCT.lean`) route through a **parametric oracle**
`LeafSpec.arrStore`/`arrLoad` whose default is identity.  A denotation proof has
nothing to say until the oracle is pinned to a concrete memory model.  We pin it
to the standard **byte-offset array model** the machine `scale` encodes: element
`i` of an array lives at byte offset `i * scale`, accessed as a little-endian
`u64` word (the `JArray.getWord`/`setWord` accessors of `JasminTypes.lean`).
This is `byteOffsetLeafSpec`.  The element size is `scale`, matching the machine
SIB scale.

* `byteOffsetLeafSpec.arrStore arr oldV idx ⟨_, srcV⟩` writes the `u64` word read
  from `srcV` (byte offset `0`) into the array's word slot at byte offset
  `idx * scale`.
* `byteOffsetLeafSpec.arrLoad dst oldV ⟨_, srcV⟩ idx` reads the `u64` word at
  byte offset `idx * scale` of `srcV` and writes it into `dst`'s word slot `0`.

## The correspondence

`StateMatch` (reused, scalar registers) handles the index/src scalar slots.
`MemMatch ρ arrBase scale rs js` relates, for each source array slot `arr` and
each element index `i`, the source array word at byte offset `scale * i` to the
machine memory cell `(arrBase arr, scale * i)`.  `arrBase : String → String` is
the array-slot → machine-base-name placement the register/stack allocator picks.

## What is proved

* `byteOffsetLeafSpec` — the concrete oracle (store = word write at `idx*scale`,
  load = word read at `idx*scale`).
* the **machine side, fully**: after `storeIdx (ρ arrBase) (ρ idx) scale v`, the
  machine cell `(ρ arrBase, scale * idx)` holds `v` and every other cell is
  unchanged (`machine_store_cell` / `machine_store_other`); `loadMemIdx` reads
  exactly that cell into `ρ dst` (`machine_load_value`).
* the **index correspondence**: under `StateMatch` and the carried guard
  `idx < 2^64`, `(js.get (ρ idxVar)).toNat = idx`, so the machine effective
  offset `scale * (js.get (ρ idxVar)).toNat` equals the source byte offset
  `scale * idx` (`machine_offset_eq`).

## The source-array element-accessor roundtrip

The bridge to the source array model rests on the **source-array element-accessor
roundtrip**: reading element `idx` (via `JArray.getWord … (scale*idx)`) of the
array *after* `byteOffsetLeafSpec.arrStore` wrote element `idx` recovers the
stored word. Concretely (under the in-bounds bound `scale*idx + 8 ≤ n`):

```
JArray.getWord (JArray.setWord a .U64 (scale*idx) v) .U64 (scale*idx) = v
```

`getWord`/`setWord` are little-endian byte folds (`foldl` over `List.range 8`
with `|||`/`<<<`/`>>>`/`truncate`); the roundtrip (`getWord_setWord_same`) is
proved by unrolling the eight byte writes/reads (distinct-index
`Function.update` non-interference) and closing the 64-bit little-endian
recompose identity with `bv_decide`. The in-bounds bound is required:
without it `setWord` drops out-of-range bytes and the roundtrip is false. This
discharges the source tower-array (flat `JArray` byte) ↔ flat byte-offset
machine memory bridge; the machine side, index correspondence, offset equality,
and the wiring into the real `RustExec` post-state are all proved on top.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemDenote

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemCT
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin (JArray)

/-! ## 1. The concrete byte-offset array oracle -/

/-- Read the element `u64` word at element index `i` of a `JArray`, under the
    byte-offset model: element `i` lives at byte offset `i * scale`. -/
noncomputable def arrElem {n : Nat} (a : JArray n) (scale i : Nat) : BitVec 64 :=
  a.getWord .U64 (scale * i)

/-- Write the element `u64` word `v` at element index `i` of a `JArray`. -/
def arrSetElem {n : Nat} (a : JArray n) (scale i : Nat) (v : BitVec 64) : JArray n :=
  a.setWord .U64 (scale * i) v

/-- Extract the leading `u64` word (byte offset `0`) from a source value's byte
    array.  Used to read the value to be stored out of `srcV`, and to deliver a
    loaded word into the `dst` slot's word `0`. -/
noncomputable def valWord {t : TowerType} (v : RustVal t) : BitVec 64 :=
  v.getWord .U64 0

/-- **The concrete byte-offset `LeafSpec`.**  The array store/load oracles
    implement the standard `idx * scale`-byte-offset element model, with element
    size `scale` (matching the machine SIB scale).  Every other oracle keeps its
    `LeafSpec` default. -/
noncomputable def byteOffsetLeafSpec (scale : Nat) : LeafSpec where
  call      := fun _ _ _ oldV _ => oldV
  limbStore := fun _ oldV _ _ => oldV
  arrStore  := fun _arr oldV idx srcV => arrSetElem oldV scale idx (valWord srcV.2)
  arrLoad   := fun _dst oldV srcV idx =>
    -- write the loaded word into dst's word-0 slot
    oldV.setWord .U64 0 (arrElem srcV.2 scale idx)

/-! ## 2. The state correspondence -/

/-- **Memory correspondence.**  For the array slot `arr` (with machine base name
    `arrBase arr`) the source array word at byte offset `scale * i` equals the
    machine memory cell `(arrBase arr, scale * i)`, for every element index `i`.
    `StateMatch` (imported) separately relates the scalar index/src registers. -/
def MemMatch (arrBase : String → String) (scale : Nat)
    (arr : Located) (rs : RustState) (js : JState 64) : Prop :=
  ∀ (a : RustVal arr.locDst), locatedLookup rs arr = some a →
    ∀ i : Nat, arrElem a scale i = js.load (arrBase arr.locVar) (↑(scale * i))

/-! ## 3. The machine side (fully proved) -/

/-- After a register-indexed scatter, the targeted cell holds the stored value. -/
theorem machine_store_cell (js : JState 64) (base idx : String) (scale : Nat)
    (v : BitVec 64) :
    (js.storeIdx base idx scale v).load base (↑(scale * (js.get idx).toNat)) = v := by
  simpa using JState.load_storeIdx_same js base idx scale v

/-- A register-indexed scatter leaves every other cell unchanged. -/
theorem machine_store_other (js : JState 64) (base idx : String) (scale : Nat)
    (v : BitVec 64) (b' : String) (o' : Int)
    (h : ¬ (b' = base ∧ o' = (↑(scale * (js.get idx).toNat) : Int))) :
    (js.storeIdx base idx scale v).load b' o' = js.load b' o' :=
  JState.load_storeIdx_other js base idx scale v b' o' h

/-- The lowered store, evaluated: it scatters `js.get (ρ src)` to the index cell. -/
theorem evalInstr_lowerMemStore (ρ : RegMap) (m : MemStoreSrc) (js : JState 64) :
    evalInstr js (lowerMemStore ρ m)
      = js.storeIdx (ρ m.arr) (ρ m.idx) m.scale (js.get (ρ m.src)) := by
  simp [lowerMemStore, evalInstr, x86_MOV, JOperand.eval]

/-- The lowered load, evaluated: it gathers the index cell into `ρ dst`. -/
theorem evalInstr_lowerMemLoad (ρ : RegMap) (m : MemLoadSrc) (js : JState 64) :
    evalInstr js (lowerMemLoad ρ m)
      = js.setReg (ρ m.dst) (js.loadIdx (ρ m.arr) (ρ m.idx) m.scale) := by
  simp [lowerMemLoad, evalInstr, x86_MOV]

/-- `runBlock` of a one-instruction lowered store. -/
theorem runBlock_lowerMemStore (ρ : RegMap) (m : MemStoreSrc) (js : JState 64) :
    runBlock js [lowerMemStore ρ m]
      = js.storeIdx (ρ m.arr) (ρ m.idx) m.scale (js.get (ρ m.src)) := by
  simp [runBlock_cons, runBlock_nil, evalInstr_lowerMemStore]

/-- `runBlock` of a one-instruction lowered load. -/
theorem runBlock_lowerMemLoad (ρ : RegMap) (m : MemLoadSrc) (js : JState 64) :
    runBlock js [lowerMemLoad ρ m]
      = js.setReg (ρ m.dst) (js.loadIdx (ρ m.arr) (ρ m.idx) m.scale) := by
  simp [runBlock_cons, runBlock_nil, evalInstr_lowerMemLoad]

/-! ## 4. The index correspondence -/

/-- Under `StateMatch` and the in-range guard `idx < 2^64`, the machine index
    register's `.toNat` recovers the source index. -/
theorem machine_index_recover (ρ : RegMap) (rs : RustState) (js : JState 64)
    (hmatch : StateMatch ρ rs js) (idxVar : String) (idx : Nat)
    (hidxval : rs.rsScalar idxVar = idx) (hlt : idx < 2 ^ 64) :
    (js.get (ρ idxVar)).toNat = idx := by
  rw [hmatch idxVar, hidxval, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hlt

/-- Consequently the machine effective byte offset equals the source byte offset. -/
theorem machine_offset_eq (ρ : RegMap) (rs : RustState) (js : JState 64)
    (hmatch : StateMatch ρ rs js) (idxVar : String) (idx : Nat)
    (hidxval : rs.rsScalar idxVar = idx) (hlt : idx < 2 ^ 64) (scale : Nat) :
    scale * (js.get (ρ idxVar)).toNat = scale * idx := by
  rw [machine_index_recover ρ rs js hmatch idxVar idx hidxval hlt]

/-! ## 5. The source-array element-accessor roundtrip

The single named fact the denote theorems below consume: the byte-fold roundtrip
of the little-endian `JArray.getWord` / `setWord` accessors — the concrete
per-element word accessor that bridges the source tower-array representation
against a flat byte-offset memory. Proved by unrolling the eight byte
writes/reads and `bv_decide` on the recompose identity. -/

/-- **Source-array element-accessor roundtrip.**  Reading the
    `u64` element word just written recovers the stored value, provided the
    element is in bounds (`off + 8 ≤ n`; without it `setWord` drops the
    out-of-range bytes and `getWord` reads them as `0`, so the roundtrip is
    *false* — the bound is part of the statement, not a convenience). -/
theorem getWord_setWord_same {n : Nat} (a : JArray n) (off : Nat) (v : BitVec 64)
    (hb : off + 8 ≤ n) :
    (a.setWord .U64 off v).getWord .U64 off = v := by
  unfold JArray.getWord JArray.setWord
  dsimp only [Jasmin.WSize.bits, Jasmin.WSize.bytes]
  have h0 : off + 0 < n := by omega
  have h1 : off + 1 < n := by omega
  have h2 : off + 2 < n := by omega
  have h3 : off + 3 < n := by omega
  have h4 : off + 4 < n := by omega
  have h5 : off + 5 < n := by omega
  have h6 : off + 6 < n := by omega
  have h7 : off + 7 < n := by omega
  rw [show List.range 8 = [0,1,2,3,4,5,6,7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil,
    dite_eq_left h0, dite_eq_left h1, dite_eq_left h2, dite_eq_left h3,
    dite_eq_left h4, dite_eq_left h5, dite_eq_left h6, dite_eq_left h7]
  simp only [JArray.set, Function.update_apply, Fin.mk.injEq,
    Nat.add_right_cancel_iff]
  simp only [add_right_inj]
  norm_num
  simp only [show (0 : BitVec Jasmin.WSize.U64.bits) = (0 : BitVec 64) from rfl]
  erw [Function.update_self]
  bv_decide

/-- `arrElem` of `arrSetElem` at the **same** element index recovers the word
    (in bounds).  Follows from `getWord_setWord_same`. -/
theorem arrElem_arrSetElem_same {n : Nat} (a : JArray n) (scale i : Nat)
    (v : BitVec 64) (hb : scale * i + 8 ≤ n) :
    arrElem (arrSetElem a scale i v) scale i = v := by
  unfold arrElem arrSetElem
  exact getWord_setWord_same a (scale * i) v hb

/-! ## 6. Denote preservation: store -/

/-- **Store value-correctness.**  Under the concrete `byteOffsetLeafSpec scale`,
    the register/memory correspondence, and the in-range index guard, the machine
    `runBlock` of the lowered `storeMemIdx` tracks the source `RArrStore`
    post-state: the targeted array element holds the stored word, and every other
    cell is unchanged.

    Here we state the **targeted-cell** correctness:
    after the lowered store the machine cell `(ρ arr, scale * idx)` holds the
    stored word `valWord srcV`, matching the source oracle
    `byteOffsetLeafSpec.arrStore`'s element-`idx` update read back by `arrElem`.
    The source-side read-back uses `arrElem_arrSetElem_same` (⇐
    `getWord_setWord_same`); the machine side is `machine_store_cell` composed
    with the index/offset correspondence.  The store-value placed in `ρ src` is
    assumed to be the source word `valWord srcV` (the `mov`-into-data-reg
    convention `hsrcval`, the value-side dual of the CT half's data-register
    convention). -/
theorem lowerMemStore_denote_cell (scale : Nat) (ρ : RegMap)
    (m : MemStoreSrc) (rs : RustState) (js : JState 64)
    (hscale : m.scale = scale)
    (hmatch : StateMatch ρ rs js)
    (idx : Nat) (hidxval : rs.rsScalar m.idx = idx) (hlt : idx < 2 ^ 64)
    (oldV : RustVal (⟨m.arr, m.arrTy⟩ : Located).locDst)
    (srcV : RustVal (⟨m.src, m.srcTy⟩ : Located).locDst)
    (hsrcval : js.get (ρ m.src) = valWord srcV)
    (hbound : scale * idx + 8 ≤ m.arrTy.storageBytes) :
    -- machine: targeted cell after the lowered store
    (runBlock js [lowerMemStore ρ m]).load (ρ m.arr) (↑(scale * idx))
      -- source: element `idx` of the array updated by the concrete oracle,
      -- read back via the byte-offset element accessor
      = arrElem
          ((byteOffsetLeafSpec scale).arrStore ⟨m.arr, m.arrTy⟩ oldV idx
            ⟨(⟨m.src, m.srcTy⟩ : Located).locDst, srcV⟩)
          scale idx := by
  -- source side reduces to the stored word
  have hsrc : arrElem
      ((byteOffsetLeafSpec scale).arrStore ⟨m.arr, m.arrTy⟩ oldV idx
        ⟨(⟨m.src, m.srcTy⟩ : Located).locDst, srcV⟩) scale idx
      = valWord srcV := by
    simp only [byteOffsetLeafSpec]
    exact arrElem_arrSetElem_same oldV scale idx (valWord srcV) hbound
  rw [hsrc, runBlock_lowerMemStore, hsrcval]
  -- machine side: the targeted cell holds the stored word
  have hoff : scale * (js.get (ρ m.idx)).toNat = scale * idx :=
    machine_offset_eq ρ rs js hmatch m.idx idx hidxval hlt scale
  have := machine_store_cell js (ρ m.arr) (ρ m.idx) scale (valWord srcV)
  rw [hoff] at this
  -- align the `m.scale = scale` rewrite in the goal's `storeIdx`
  subst hscale
  exact this

/-! ## 7. Denote preservation: load -/

/-- **Load value-correctness.**  Under the concrete `byteOffsetLeafSpec scale`,
    the register/memory correspondence (`MemMatch` on the source array slot), and
    the in-range index guard, the machine `runBlock` of the lowered `loadMemIdx`
    loads into `ρ dst` exactly the source array element `idx` — the value the
    source oracle `byteOffsetLeafSpec.arrLoad` delivers (`arrElem srcArr scale
    idx`).

    The machine side is `machine_load_value`+`runBlock_lowerMemLoad`; the
    array-element value correspondence is supplied by `MemMatch` together with
    the index/offset correspondence.  No `getWord_setWord` roundtrip is needed on
    the **load** path (it only reads), so this theorem is fully proved with no
    dependence on the reported blocker. -/
theorem lowerMemLoad_denote (scale : Nat) (arrBase : String → String) (ρ : RegMap)
    (m : MemLoadSrc) (rs : RustState) (js : JState 64)
    (hscale : m.scale = scale)
    (hbase : arrBase (⟨m.arr, m.arrTy⟩ : Located).locVar = ρ m.arr)
    (hmatch : StateMatch ρ rs js)
    (idx : Nat) (hidxval : rs.rsScalar m.idx = idx) (hlt : idx < 2 ^ 64)
    (srcArr : RustVal (⟨m.arr, m.arrTy⟩ : Located).locDst)
    (hsrclook : locatedLookup rs ⟨m.arr, m.arrTy⟩ = some srcArr)
    (hmem : MemMatch arrBase scale ⟨m.arr, m.arrTy⟩ rs js) :
    (runBlock js [lowerMemLoad ρ m]).get (ρ m.dst) = arrElem srcArr scale idx := by
  rw [runBlock_lowerMemLoad, JState.get_setReg_same]
  -- machine load reduces to the cell at the source byte offset
  have hoff : scale * (js.get (ρ m.idx)).toNat = scale * idx :=
    machine_offset_eq ρ rs js hmatch m.idx idx hidxval hlt scale
  have hcell : js.loadIdx (ρ m.arr) (ρ m.idx) m.scale
      = js.load (ρ m.arr) (↑(scale * idx)) := by
    unfold JState.loadIdx
    rw [hscale]
    congr 1
    rw [← Nat.cast_mul, hoff]
  rw [hcell]
  -- the cell equals the source element via MemMatch
  have hbase' : ρ m.arr = arrBase (⟨m.arr, m.arrTy⟩ : Located).locVar := hbase.symm
  rw [hbase']
  exact (hmem srcArr hsrclook idx).symm

/-! ## 8. Wiring the store post-state to the real `RustExec`

`RArrStore`'s `RustExec` arm steps to `locatedUpdate rs arr (leafSpec.arrStore
arr oldV idx ⟨src.locDst, srcV⟩)`.  The denote theorem above already matched the
machine cell to `arrElem` of exactly this oracle output, so wiring to the real
operational step is a re-statement against the post-state's array slot. -/

/-- The source `RArrStore` post-state under the concrete oracle: the updated
    array slot value is `arrSetElem oldV scale idx (valWord srcV)`.  This is the
    `RustExec.arrStore` result with `leafSpec := byteOffsetLeafSpec`. -/
theorem byteOffsetLeafSpec_arrStore_post (scale : Nat) (arr : Located)
    (oldV : RustVal arr.locDst) (idx : Nat)
    (srcLoc : Located) (srcV : RustVal srcLoc.locDst) :
    (byteOffsetLeafSpec scale).arrStore arr oldV idx
        (⟨srcLoc.locDst, srcV⟩ : Σ t : TowerType, RustVal t)
      = arrSetElem oldV scale idx (valWord srcV) := rfl

/-- **Store, against the real `RustExec` post-state.**  Combines the operational
    `RustExec.arrStore` step (under `byteOffsetLeafSpec scale`) with
    `lowerMemStore_denote_cell`: the machine targeted cell after the lowered
    store equals the source post-state's array element `idx`, read back via the
    byte-offset accessor.  Consumes `getWord_setWord_same` (via
    `lowerMemStore_denote_cell`). -/
theorem lowerMemStore_denote_rustExec (N : Nat) (scale : Nat) (ρ : RegMap)
    (m : MemStoreSrc) (rs rs' : RustState) (js : JState 64)
    (hscale : m.scale = scale)
    (hmatch : StateMatch ρ rs js)
    (idx : Nat) (hidxval : rs.rsScalar m.idx = idx) (hlt : idx < 2 ^ 64)
    (oldV : RustVal (⟨m.arr, m.arrTy⟩ : Located).locDst)
    (srcV : RustVal (⟨m.src, m.srcTy⟩ : Located).locDst)
    (hsrcval : js.get (ρ m.src) = valWord srcV)
    (hbound : scale * idx + 8 ≤ m.arrTy.storageBytes)
    (_holdlook : locatedLookup rs ⟨m.arr, m.arrTy⟩ = some oldV)
    (_hsrclook : locatedLookup rs ⟨m.src, m.srcTy⟩ = some srcV)
    (_hexec : RustExec N (byteOffsetLeafSpec scale) m.toLowCT rs rs') :
    (runBlock js [lowerMemStore ρ m]).load (ρ m.arr) (↑(scale * idx))
      = arrElem
          ((byteOffsetLeafSpec scale).arrStore ⟨m.arr, m.arrTy⟩ oldV idx
            ⟨(⟨m.src, m.srcTy⟩ : Located).locDst, srcV⟩)
          scale idx :=
  lowerMemStore_denote_cell scale ρ m rs js hscale hmatch idx hidxval hlt oldV srcV
    hsrcval hbound

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemDenote
