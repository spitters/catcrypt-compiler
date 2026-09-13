/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridge
public import CatCrypt.Crypto.SecureCompilation.Ascent.ArrStoreLeaf
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMulx

/-!
# The value-level middle tie for the array-memory fragment (Route B, memory axis)

`arith_middle_tie_at_dst` (`CorresBridgeArith.lean`) discharges the value-level
core of `corresJ_forget_to_corres`'s `hmirror` for the **arithmetic** fragment,
reading the output register `dst` through the forgetful register view `regEnv`.
`regEnv`, however, **forgets the `JState` memory axis entirely** — it maps only
registers (`fun r => some ⟨.sword 64, st.regs r⟩`). The dynamic-index array
read/write arms of `semScalar` (`RArrLoad`/`RArrStore`) read a `.memref n` slot,
which `regEnv` cannot supply. This module builds the **memory-inclusive**
forgetful view and proves the memory analogue of the arithmetic tie.

## The memory-inclusive forgetful view (`regMemEnv`)

`regMemEnv st regionName n scale` carries the `JState` memory of one array region
into an `SEnvScalar` `.memref n` slot — element `j` is the machine word at byte
offset `scale · j` of the region `regionName` (`st.mem regionName (scale·j)`) —
while every other name reads its register at `.sword 64` exactly as `regEnv`
does. This is the `HL` (heap-abstraction) twin of `regEnv`'s `L2`
register-lifting: the memory the register view forgot is a memref
variable, so `semScalar`'s `RArrLoad`/`RArrStore` arm can be run over it.

## The crux (`mem_load_middle_tie_at_dst`)

For a dynamic-index array read `dst := src[idx]`, both output values reduce to the
**same** machine memory word `st.mem m.arr (scale · i)`:

* on the scalar side, `semScalar`'s `RArrLoad` arm writes `memGetDyn arr i.toNat`
  where `arr` is the memref slot of `regMemEnv`; on an in-range index this reduces
  (`memGetDyn_regionArr`) to `st.mem m.arr (scale · i.toNat)` — the read value
  comes from `st.mem`;
* on the machine side, `runBlock` of the lowered gather `lowerMemLoad idRho m`
  loads `st.loadIdx m.arr m.idx scale = st.mem m.arr (scale · (st.regs m.idx))`
  into `ρ dst` (`runBlock_lowerMemLoad`).

The index word is the SAME on both sides (`i = st.regs m.idx`, since `regMemEnv`
reads the index register at `.sword 64` and `idRho = id`), so the two agree
without any register-map fiction.

## The store round-trip tie (`mem_store_middle_tie_at_cell`)

For a dynamic-index array write `arr[idx] := src`, running `semScalar`'s
`RArrStore` arm updates the memref slot with `memSetDyn a i.toNat v`; reading that
cell back (`memGetDyn … i.toNat`) recovers `v = st.regs m.src`. The machine store
`runBlock (lowerMemStore idRho m)` scatters the same `st.regs m.src` to
`st.mem m.arr (scale · i)`; reading that machine cell back also recovers
`st.regs m.src`. Both round-trip to the source word — the write landed in the
matching cell on both machines.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (semScalar SEnvScalar)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMulx (idRho)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemCT
  (MemLoadSrc MemStoreSrc lowerMemLoad lowerMemStore)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemDenote
  (runBlock_lowerMemLoad runBlock_lowerMemStore)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (encodeTy)

/-! ## The memory-inclusive forgetful view -/

/-- **The memory-inclusive forgetful view.** `regMemEnv st regionName n scale`
    reads the `JState` register file as scalar `.sword 64` words (exactly as
    `regEnv`), **and additionally** carries the memory region `regionName` into a
    `.memref n` slot: element `j` is the machine word at byte offset `scale · j`
    (`st.mem regionName (scale · j)`). The `HL`/heap-abstraction twin of
    `regEnv`, supplying the memref slot that `regEnv` forgets and that
    `semScalar`'s `RArrLoad`/`RArrStore` arm requires. -/
def regMemEnv (st : JState 64) (regionName : String) (n scale : Nat) : SEnvScalar :=
  fun r =>
    if r = regionName then
      some ⟨.memref n, fun j : Fin n => st.mem regionName (scale * j.val)⟩
    else
      some ⟨.sword 64, st.regs r⟩

/-- The region name resolves to the `.memref n` slot holding the byte-offset view
    of the machine memory region. -/
theorem regMemEnv_region (st : JState 64) (regionName : String) (n scale : Nat) :
    regMemEnv st regionName n scale regionName
      = some ⟨.memref n, fun j : Fin n => st.mem regionName (scale * j.val)⟩ := by
  simp [regMemEnv]

/-- Every name other than the region reads its register at `.sword 64`, exactly as
    `regEnv` does — `regMemEnv` extends `regEnv` on the single memory slot. -/
theorem regMemEnv_reg (st : JState 64) (regionName : String) (n scale : Nat)
    (r : String) (h : r ≠ regionName) :
    regMemEnv st regionName n scale r = some ⟨.sword 64, st.regs r⟩ := by
  simp [regMemEnv, h]

/-- **`memGetDyn` reduction over the view.** On an in-range index `k < n`, reading
    element `k` of `regMemEnv`'s memref slot recovers the machine memory word at
    byte offset `scale · k` — the `memGetDyn` index-modulo collapses (`k < n`) to
    the raw cell, so the read value comes from `st.mem`. -/
theorem memGetDyn_regionArr (st : JState 64) (regionName : String) (n scale k : Nat)
    (hk : k < n) :
    memGetDyn (fun j : Fin n => st.mem regionName (scale * j.val)) k
      = st.mem regionName (scale * k) := by
  cases n with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ m =>
      simp only [memGetDyn]
      rw [Nat.mod_eq_of_lt hk]

/-! ## The machine side -/

/-- **The machine output register of the lowered array-load.** Running the lowered
    register-indexed gather `lowerMemLoad idRho m` from `st` leaves the destination
    register `m.dst` holding the machine memory word at byte offset
    `scale · (st.regs m.idx)` of the array-base region `m.arr`. -/
theorem runBlock_lowerMemLoad_get (m : MemLoadSrc) (st : JState 64) :
    (runBlock st [lowerMemLoad idRho m]).get (idRho m.dst)
      = st.mem m.arr (m.scale * (st.regs m.idx).toNat) := by
  rw [runBlock_lowerMemLoad, JState.get_setReg_same]
  simp only [idRho, id_eq, JState.loadIdx, JState.load, JState.get]

/-- **The machine memory cell of the lowered array-store.** Running the lowered
    register-indexed scatter `lowerMemStore idRho m` from `st` leaves the machine
    memory cell at byte offset `scale · (st.regs m.idx)` of the region `m.arr`
    holding the scattered source word `st.regs m.src`. -/
theorem runBlock_lowerMemStore_cell (m : MemStoreSrc) (st : JState 64) :
    (runBlock st [lowerMemStore idRho m]).load m.arr (m.scale * (st.regs m.idx).toNat)
      = st.regs m.src := by
  rw [runBlock_lowerMemStore]
  simp only [idRho, id_eq, JState.get]
  exact JState.load_storeIdx_same st m.arr m.idx m.scale (st.regs m.src)

/-! ## The value-level middle ties -/

/-- **The value-level middle tie for the array-load.** `semScalar` succeeds on the
    real `LowCT` node `MemLoadSrc.toLowCT m = RArrLoad ⟨dst⟩ ⟨arr⟩ idx` over the
    memory-inclusive view `regMemEnv st m.arr n m.scale`, and the value it writes
    at the output slot `m.dst` is exactly the machine's output register
    `(runBlock st [lowerMemLoad idRho m]).get (idRho m.dst)` — both equal the
    machine memory word `st.mem m.arr (scale · (st.regs m.idx))`.

    The side conditions: the destination is a `u64` (`hdst`, selecting the real
    load arm), the index register is distinct from the array region (`hidx_ne`, so
    the view reads it at `.sword 64`), and the index is in range (`hidx_lt`, so
    `memGetDyn`'s modulo collapses and the read hits `st.mem`). The
    memory analogue of `arith_middle_tie_at_dst`. -/
theorem mem_load_middle_tie_at_dst (m : MemLoadSrc) (st : JState 64) (n : Nat)
    (hdst : m.dstTy = .TU64) (hidx_ne : m.idx ≠ m.arr)
    (hidx_lt : (st.regs m.idx).toNat < n) :
    (∃ env', semScalar (MemLoadSrc.toLowCT m) (regMemEnv st m.arr n m.scale) = some env'
      ∧ env' m.dst
          = some ⟨.sword 64, (runBlock st [lowerMemLoad idRho m]).get (idRho m.dst)⟩) := by
  have hArr := regMemEnv_region st m.arr n m.scale
  have hIdx := regMemEnv_reg st m.arr n m.scale m.idx hidx_ne
  refine ⟨(regMemEnv st m.arr n m.scale).upd m.dst (t := .sword 64)
      (memGetDyn (fun j : Fin n => st.mem m.arr (m.scale * j.val))
        (st.regs m.idx).toNat), ?_, ?_⟩
  · -- `semScalar` reduces along the destination-type guard + the two known lookups.
    simp only [MemLoadSrc.toLowCT, semScalar, hdst, hArr, hIdx]
  · -- the written value at `m.dst` equals the machine's output register.
    rw [runBlock_lowerMemLoad_get]
    simp only [SEnvScalar.upd, if_pos]
    rw [memGetDyn_regionArr st m.arr n m.scale (st.regs m.idx).toNat hidx_lt]

/-- **The store round-trip middle tie for the array-store.** `semScalar` succeeds on
    the real `LowCT` node `MemStoreSrc.toLowCT m = RArrStore ⟨arr⟩ idx ⟨src⟩` over
    the memory-inclusive view, updating the memref slot with
    `memSetDyn a i.toNat v` (`v = st.regs m.src`). Reading that cell back
    (`memGetDyn … i.toNat`, in range) recovers `st.regs m.src`; the machine store
    `runBlock [lowerMemStore idRho m]` scatters the same `st.regs m.src` to the
    matching machine cell, which also reads back to `st.regs m.src`. Both machines
    round-trip the write to the same source word — the store landed in the matching
    cell on both sides.

    The side conditions mirror the load: the array region encodes to `.memref n`
    (`harr`, selecting the real store arm), the index and source registers are
    distinct from the array region (`hidx_ne`/`hsrc_ne`, so the view reads them at
    `.sword 64`), and the index is in range (`hidx_lt`). -/
theorem mem_store_middle_tie_at_cell (m : MemStoreSrc) (st : JState 64) (n : Nat)
    (harr : encodeTy m.arrTy = .memref n)
    (hidx_ne : m.idx ≠ m.arr) (hsrc_ne : m.src ≠ m.arr)
    (hidx_lt : (st.regs m.idx).toNat < n) :
    (∃ env', semScalar (MemStoreSrc.toLowCT m) (regMemEnv st m.arr n m.scale) = some env'
      ∧ (∃ arr' : Fin n → BitVec 64, env' m.arr = some ⟨.memref n, arr'⟩
          ∧ memGetDyn arr' (st.regs m.idx).toNat
              = (runBlock st [lowerMemStore idRho m]).load m.arr
                  (m.scale * (st.regs m.idx).toNat))) := by
  have hArr := regMemEnv_region st m.arr n m.scale
  have hIdx := regMemEnv_reg st m.arr n m.scale m.idx hidx_ne
  have hSrc := regMemEnv_reg st m.arr n m.scale m.src hsrc_ne
  refine ⟨(regMemEnv st m.arr n m.scale).upd m.arr (t := encodeTy m.arrTy)
      (harr.symm ▸ memSetDyn (fun j : Fin n => st.mem m.arr (m.scale * j.val))
        (st.regs m.idx).toNat (st.regs m.src)), ?_, ?_⟩
  · -- `semScalar` reduces along the three lookups + the `.memref n` encoding guard.
    simp only [MemStoreSrc.toLowCT, semScalar, hArr, hIdx, hSrc, harr, dif_pos]
  · -- the post-env memref cell reads back to the machine's stored word.
    refine ⟨memSetDyn (fun j : Fin n => st.mem m.arr (m.scale * j.val))
      (st.regs m.idx).toNat (st.regs m.src), ?_, ?_⟩
    · -- the memref slot after the update (cast collapsed).
      simp only [SEnvScalar.upd, if_pos]
      exact congrArg some
        (sigma_memref harr
          (memSetDyn (fun j : Fin n => st.mem m.arr (m.scale * j.val))
            (st.regs m.idx).toNat (st.regs m.src)))
    · -- both round-trip to the source word.
      rw [runBlock_lowerMemStore_cell]
      cases n with
      | zero => exact absurd hidx_lt (Nat.not_lt_zero _)
      | succ p => simp [memGetDyn, memSetDyn]

end CatCrypt.Crypto.SecureCompilation.Ascent
