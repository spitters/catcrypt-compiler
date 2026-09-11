/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridgeMem

/-!
# The full cell-by-cell store correspondence (Route B, memory axis)

`mem_store_middle_tie_at_cell` (`CorresBridgeMem.lean`) discharges the value-level
core of the array-**store** middle tie, but only at the **written** cell: it shows
that the cell the write targets round-trips to the source word `st.regs m.src` on
both machines. It says nothing about the rest of the region.

This module upgrades the store round-trip to a **full memory correspondence**:
after `semScalar (MemStoreSrc.toLowCT m)` on the memory-inclusive view
`regMemEnv st m.arr n m.scale` and after `runBlock st [lowerMemStore idRho m]`,
the whole post-region agrees **cell by cell** — the `.memref n` slot of the
scalar result env, read at cell `j`, equals the machine memory word at byte
offset `m.scale · j` of region `m.arr`, for *every* `j : Fin n`, not just the
written one.

## The two off-cell ingredients

* **Machine side (`runBlock_lowerMemStore_other`).** The lowered scatter changes
  memory only at byte offset `m.scale · (st.regs m.idx)`; every other byte offset
  reads back to `st.mem` unchanged (`JState.load_storeIdx_other`).
* **Source side (`memSetDyn`).** `semScalar`'s `RArrStore` arm updates the memref
  slot with `memSetDyn a i v`, which changes only cell `i.toNat` and leaves every
  other `Fin n` cell equal to `a`.

## Scale-injectivity

Lining cell `j` up with byte offset `m.scale · j` needs distinct in-range cells to
land at distinct byte offsets: an off-cell `j ≠ idx` must satisfy
`m.scale · j ≠ m.scale · idx`, so the machine store at `m.scale · idx` leaves it
untouched. This holds exactly when `0 < m.scale` (`hscale`, an explicit honest
hypothesis) — `Nat.eq_of_mul_eq_mul_left`.

The written cell reuses `mem_store_middle_tie_at_cell` (both sides
`st.regs m.src`); every other cell is preserved to `st.mem m.arr (m.scale · j)`,
a genuine machine memory read, on both sides.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (semScalar SEnvScalar)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMulx (idRho)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemCT
  (MemStoreSrc lowerMemStore)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemDenote
  (runBlock_lowerMemStore)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (encodeTy)

/-! ## The off-cell machine lemma -/

/-- **Off-cell preservation, machine side.** The lowered register-indexed scatter
    `lowerMemStore idRho m` writes memory only at byte offset
    `m.scale · (st.regs m.idx)` of region `m.arr`; at any *other* byte offset `off`
    the machine memory reads back to `st.mem` unchanged. The store touches one
    cell — every disjoint cell survives. -/
theorem runBlock_lowerMemStore_other (m : MemStoreSrc) (st : JState 64) (off : Int)
    (h : off ≠ ((m.scale * (st.regs m.idx).toNat : Nat) : Int)) :
    (runBlock st [lowerMemStore idRho m]).load m.arr off = st.mem m.arr off := by
  rw [runBlock_lowerMemStore]
  simp only [idRho, id_eq, JState.get]
  rw [JState.load_storeIdx_other st m.arr m.idx m.scale (st.regs m.src) m.arr off
    (by rintro ⟨-, heq⟩; exact h heq)]
  rfl

/-! ## The full cell-by-cell store correspondence -/

/-- **The full store middle tie.** `semScalar (MemStoreSrc.toLowCT m)` succeeds on
    the memory-inclusive view `regMemEnv st m.arr n m.scale`, and the `.memref n`
    slot of the resulting env agrees **cell by cell** with the machine memory of
    `runBlock st [lowerMemStore idRho m]`: for every `j : Fin n`, the env cell `j`
    equals the machine word at byte offset `m.scale · j` of region `m.arr`.

    The written cell `j` with `m.scale · j = m.scale · idx` carries the scattered
    source word `st.regs m.src` (via `mem_store_middle_tie_at_cell`); every other
    cell is preserved to the genuine machine read `st.mem m.arr (m.scale · j)` — on
    the source side because `memSetDyn` touches only the index cell, on the machine
    side because the scatter touches only offset `m.scale · idx`
    (`runBlock_lowerMemStore_other`), the two lined up by scale-injectivity
    (`0 < m.scale`).

    Side conditions mirror `mem_store_middle_tie_at_cell` — the array region
    encodes to `.memref n` (`harr`), index/source registers distinct from the
    region (`hidx_ne`/`hsrc_ne`), index in range (`hidx_lt`) — plus the honest
    scale-positivity `hscale : 0 < m.scale` that makes distinct in-range cells map
    to distinct byte offsets. -/
theorem mem_store_middle_tie_full (m : MemStoreSrc) (st : JState 64) (n : Nat)
    (harr : encodeTy m.arrTy = .memref n)
    (hidx_ne : m.idx ≠ m.arr) (hsrc_ne : m.src ≠ m.arr)
    (hidx_lt : (st.regs m.idx).toNat < n) (hscale : 0 < m.scale) :
    (∃ env', semScalar (MemStoreSrc.toLowCT m) (regMemEnv st m.arr n m.scale) = some env'
      ∧ (∃ arr' : Fin n → BitVec 64, env' m.arr = some ⟨.memref n, arr'⟩
          ∧ ∀ j : Fin n, arr' j
              = (runBlock st [lowerMemStore idRho m]).load m.arr
                  ((m.scale * j.val : Nat) : Int))) := by
  have hArr := regMemEnv_region st m.arr n m.scale
  have hIdx := regMemEnv_reg st m.arr n m.scale m.idx hidx_ne
  have hSrc := regMemEnv_reg st m.arr n m.scale m.src hsrc_ne
  refine ⟨(regMemEnv st m.arr n m.scale).upd m.arr (t := encodeTy m.arrTy)
      (harr.symm ▸ memSetDyn (fun j : Fin n => st.mem m.arr (m.scale * j.val))
        (st.regs m.idx).toNat (st.regs m.src)), ?_, ?_⟩
  · -- `semScalar` reduces along the three lookups + the `.memref n` encoding guard.
    simp only [MemStoreSrc.toLowCT, semScalar, hArr, hIdx, hSrc, harr, dif_pos]
  · -- extract the post-env memref slot, then match it cell by cell.
    refine ⟨memSetDyn (fun j : Fin n => st.mem m.arr (m.scale * j.val))
      (st.regs m.idx).toNat (st.regs m.src), ?_, ?_⟩
    · -- the memref slot after the update (dependent cast collapsed).
      simp only [SEnvScalar.upd, if_pos]
      exact congrArg some
        (sigma_memref harr
          (memSetDyn (fun j : Fin n => st.mem m.arr (m.scale * j.val))
            (st.regs m.idx).toNat (st.regs m.src)))
    · -- cell-by-cell: written cell → source word; off-cell → preserved machine read.
      intro j
      cases n with
      | zero => exact absurd hidx_lt (Nat.not_lt_zero _)
      | succ p =>
          have hk : (st.regs m.idx).toNat % (p + 1) = (st.regs m.idx).toNat :=
            Nat.mod_eq_of_lt hidx_lt
          simp only [memSetDyn]
          by_cases hj : j.val = (st.regs m.idx).toNat
          · -- the written cell: both sides are `st.regs m.src`.
            have hjfin : j = ⟨(st.regs m.idx).toNat % (p + 1),
                Nat.mod_lt _ (Nat.succ_pos p)⟩ := by
              apply Fin.ext; rw [hj]; exact hk.symm
            rw [if_pos hjfin]
            rw [show ((m.scale * j.val : Nat) : Int)
                  = ((m.scale * (st.regs m.idx).toNat : Nat) : Int) from by rw [hj]]
            exact (runBlock_lowerMemStore_cell m st).symm
          · -- an off-cell: preserved to the machine read `st.mem m.arr (m.scale · j)`.
            have hjfin : ¬ (j = ⟨(st.regs m.idx).toNat % (p + 1),
                Nat.mod_lt _ (Nat.succ_pos p)⟩) := by
              intro h; apply hj; rw [h]; exact hk
            have hne : ((m.scale * j.val : Nat) : Int)
                ≠ ((m.scale * (st.regs m.idx).toNat : Nat) : Int) := by
              intro heq
              have hnat : m.scale * j.val = m.scale * (st.regs m.idx).toNat := by
                exact_mod_cast heq
              exact hj (Nat.eq_of_mul_eq_mul_left hscale hnat)
            rw [if_neg hjfin,
              runBlock_lowerMemStore_other m st ((m.scale * j.val : Nat) : Int) hne]
            simp only [Nat.cast_mul]

end CatCrypt.Crypto.SecureCompilation.Ascent
