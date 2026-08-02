/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
import Mathlib.Tactic.Ring

/-!
# The array-load value leaf for the ascent calculus

Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf
(`sgraf812/ascent`).

This is the **read dual** of `ArrStoreLeaf.lean`'s `corres_arrStore`. Where the
store leaf abstracts one dynamic-index array write `RArrStore arr idxVar src`, this
module abstracts one dynamic-index array read `RArrLoad dst src idxVar`. `semScalar`
genuinely interprets `RArrLoad`: in its real arm — destination a `u64`, source a
`.memref n`, index a `.sword 64` word — it writes the dynamic-index read
`memGetDyn arr i` into the `.sword 64` destination. This module welds a `Corres`
value leaf to that arm, mirroring the store side.

## The abstract array-read relation

`AArrLoad n` carries the array as a length-`n` vector over `ZMod 2^64`, the
abstract load index, and the destination word. `SRarrLoad` ties three concrete
names — the array slot (`.memref n`), the index word, the destination word — to
those three abstract components through `wEnc`, pointwise on the array.
`memGetDynAbs` is the abstract twin of the dialect's `memGetDyn`; the key lemma
`wEnc_memGetDyn` is that `wEnc` intertwines the two: the encoding of the concrete
dynamic-index read equals the abstract array index of the encoding. This is the
read dual of `wEnc_memSetDyn`.

## The leaf

`corres_arrLoad` proves `Corres SRarrLoad … (writes the destination component to
`arr[idx]` via `memGetDynAbs`) (.RArrLoad dst src idxVar)`: from a concrete
`SEnvScalar` related by `SRarrLoad` to an abstract `AArrLoad`, running the load
under the real `semScalar` lands in a state whose destination holds the abstract
array index `arr[idx]`. This is the read analogue of `corres_arrStore`.
-/

set_option autoImplicit false

open scoped ENNReal

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Transfer
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (semScalar SEnvScalar)

/-! ## The abstract array-read state and access -/

/-- Abstract array-machine state for the load leaf: the array's abstract value
    (a length-`n` vector over `ZMod 2^64`), the abstract load index, and the
    abstract destination word. The read-oriented twin of the store leaf's `AArr`
    (whose third component is a source word rather than a destination word). -/
structure AArrLoad (n : Nat) where
  /-- The array's abstract value, `wEnc`-encoded pointwise. -/
  arr : Fin n → ZMod (2 ^ 64)
  /-- The abstract load index (`iv.toNat`). -/
  idx : Nat
  /-- The abstract destination word (`wEnc dv`). -/
  dst : ZMod (2 ^ 64)

/-- The abstract twin of the dialect's `memGetDyn`: read element `k mod n` of an
    abstract array; `0` on the empty array. Matches `memGetDyn` structurally, so
    `wEnc` intertwines the two (`wEnc_memGetDyn`). -/
def memGetDynAbs {n : Nat} (A : Fin n → ZMod (2 ^ 64)) (k : Nat) : ZMod (2 ^ 64) :=
  match n, A with
  | 0, _ => 0
  | (m + 1), A => A ⟨k % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

/-- **Key lemma.** `wEnc` intertwines the concrete `memGetDyn` with the abstract
    `memGetDynAbs`: on a pointwise `wEnc`-related array `av ↔ A`, the encoding of
    the concrete dynamic-index read equals the abstract read of the encoding. The
    read dual of `wEnc_memSetDyn`. -/
theorem wEnc_memGetDyn {n : Nat} (av : Fin n → BitVec 64) (A : Fin n → ZMod (2 ^ 64))
    (hA : ∀ j, wEnc (av j) = A j) (k : Nat) :
    wEnc (memGetDyn av k) = memGetDynAbs A k := by
  cases n with
  | zero => simp only [memGetDyn, memGetDynAbs, wEnc]; rfl
  | succ m =>
      simp only [memGetDyn, memGetDynAbs]
      exact hA _

/-! ## The array-load state relation -/

/-- The array-load state relation: three concrete names — `arrName` (a `.memref n`
    slot), `idxName` (the index word) and `dstName` (the destination word) — are
    tied to the abstract `AArrLoad n` through `wEnc`, pointwise on the array. The
    read-oriented twin of `SRarr`. -/
def SRarrLoad (n : Nat) (arrName idxName dstName : String)
    (env : SEnvScalar) (a : AArrLoad n) : Prop :=
  (∃ av : Fin n → BitVec 64,
      env arrName = some ⟨.memref n, av⟩ ∧ ∀ j, wEnc (av j) = a.arr j) ∧
  (∃ iv : BitVec 64, env idxName = some ⟨.sword 64, iv⟩ ∧ iv.toNat = a.idx) ∧
  (∃ dv : BitVec 64, env dstName = some ⟨.sword 64, dv⟩ ∧ wEnc dv = a.dst)

/-! ## The value leaf -/

/-- **`corres_arrLoad`.** The `Corres` value leaf for the dynamic-index array read
    `RArrLoad dst src idxVar`. From a concrete `SEnvScalar` related by `SRarrLoad`
    to an abstract `AArrLoad`, running the load under the real `semScalar` lands in
    a state whose destination holds the abstract array index `arr[idx]` (the `dst`
    component updated via `memGetDynAbs`). The read analogue of `corres_arrStore`.
    The side conditions: the destination is a `u64` (`hdst`, selecting `semScalar`'s
    real load arm), and the destination slot is distinct from the array and index
    slots (`hne_arr`/`hne_idx`), so the load preserves them. -/
theorem corres_arrLoad {n : Nat} (dst src : Located) (idxVar : String)
    (hdst : dst.locDst = .TU64)
    (hne_arr : dst.locVar ≠ src.locVar) (hne_idx : dst.locVar ≠ idxVar) :
    Corres (SRarrLoad n src.locVar idxVar dst.locVar) (fun _ => True)
      (fun a => { a with dst := memGetDynAbs a.arr a.idx })
      (.RArrLoad dst src idxVar) := by
  intro env a hSR _
  obtain ⟨⟨av, hArr, hArrEnc⟩, ⟨iv, hIdx, hIdxEnc⟩, ⟨dv, hDst, hDstEnc⟩⟩ := hSR
  refine ⟨env.upd dst.locVar (t := .sword 64) (memGetDyn av iv.toNat), ?_, ?_⟩
  · -- semScalar reduces along the destination-type guard + the two known lookups.
    simp only [semScalar, hdst, hArr, hIdx]
  · -- the post-state is `SRarrLoad`-related to the abstract array read.
    refine ⟨⟨av, ?_, hArrEnc⟩, ⟨iv, ?_, hIdxEnc⟩, ⟨memGetDyn av iv.toNat, ?_, ?_⟩⟩
    · -- array slot preserved (distinct from the destination slot).
      simp only [SEnvScalar.upd, if_neg (Ne.symm hne_arr), hArr]
    · -- index slot preserved (distinct from the destination slot).
      simp only [SEnvScalar.upd, if_neg (Ne.symm hne_idx), hIdx]
    · -- env' at the destination slot holds the concrete dynamic-index read.
      simp only [SEnvScalar.upd, if_true]
    · -- the loaded word's encoding = the abstract array read.
      rw [wEnc_memGetDyn av a.arr hArrEnc iv.toNat, hIdxEnc]

end CatCrypt.Crypto.SecureCompilation.Ascent
