/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
public import Mathlib.Tactic.Ring

/-!
# The array-store value leaf for the ascent calculus

Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf
(`sgraf812/ascent`).

`Ascent/Corres.lean` registers `Corres` value leaves for the scalar arms
(`RScalarSet`/`RScalarSetExpr`) and control (`Control.lean` for
`RIfNz`/`RFor`), but — as `LoopSourceTower.lean` records — **none for the
dynamic-index array-write `RArrStore`**. `semScalar` genuinely interprets
`RArrStore` (`arrStore_executes`), so the loop/array tower delivers a live
array image, but the ascent had no keystone to weld it to. This module closes
that first loop/array frontier gap: a `Corres` value leaf that abstracts one
`RArrStore arr idxVar src` step to the array-update `arr[idx] := src`.

## The abstract array-update relation

Mirroring `SRword` (name ↦ `wEnc`-encoded word), the array leaf runs over an
abstract state `AArr n` carrying the array as a length-`n` vector over
`ZMod 2^64`, the abstract store index, and the abstract source word. `SRarr`
ties three concrete names — the array slot, the index word, the source word —
to those three abstract components through `wEnc`, pointwise on the array.
`memSetDynAbs` is the abstract twin of the dialect's `memSetDyn`; the key lemma
`wEnc_memSetDyn` is that `wEnc` intertwines the two: the encoding of the
concrete store equals the abstract store of the encoding.

## The leaf

`corres_arrStore` proves `Corres SRarr … (updates the `arr` component via
`memSetDynAbs`) (.RArrStore arr idxVar src)`: from a concrete `SEnvScalar`
related by `SRarr` to an abstract `AArr`, running the store under the real
`semScalar` lands in a state related to the abstract array-update. This is the
array analogue of `corres_setScalar`/`corres_setExpr`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Transfer
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (encodeTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memSetDyn)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (semScalar SEnvScalar)

/-! ## The abstract array state and update -/

/-- Abstract array-machine state for the store leaf: the array's abstract value
    (a length-`n` vector over `ZMod 2^64`), the abstract store index, and the
    abstract source word. The array analogue of the single `ZMod 2^64` that a
    scalar name abstracts to. -/
structure AArr (n : Nat) where
  /-- The array's abstract value, `wEnc`-encoded pointwise. -/
  arr : Fin n → ZMod (2 ^ 64)
  /-- The abstract store index (`iv.toNat`). -/
  idx : Nat
  /-- The abstract source word (`wEnc sv`). -/
  src : ZMod (2 ^ 64)

/-- The abstract twin of the dialect's `memSetDyn`: functionally update element
    `k mod n` of an abstract array; identity shape on the empty array. Matches
    `memSetDyn` structurally, so `wEnc` intertwines the two (`wEnc_memSetDyn`). -/
def memSetDynAbs {n : Nat} (A : Fin n → ZMod (2 ^ 64)) (k : Nat) (v : ZMod (2 ^ 64)) :
    Fin n → ZMod (2 ^ 64) :=
  match n, A with
  | 0, _ => fun _ => 0
  | (m + 1), A =>
      fun j => if j = ⟨k % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩ then v else A j

/-- **Key lemma.** `wEnc` intertwines the concrete `memSetDyn` with the abstract
    `memSetDynAbs`: on a pointwise `wEnc`-related array `av ↔ A`, the encoding of
    the concrete store equals the abstract store of the encoding. This is the
    ParamTransfer value-representation content the array leaf rests on. -/
theorem wEnc_memSetDyn {n : Nat} (av : Fin n → BitVec 64) (A : Fin n → ZMod (2 ^ 64))
    (hA : ∀ j, wEnc (av j) = A j) (k : Nat) (sv : BitVec 64) (j : Fin n) :
    wEnc (memSetDyn av k sv j) = memSetDynAbs A k (wEnc sv) j := by
  cases n with
  | zero => exact j.elim0
  | succ m =>
      simp only [memSetDyn, memSetDynAbs]
      by_cases hj : j = ⟨k % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
      · simp [hj]
      · simp [hj, hA j]

/-! ## The array-store state relation -/

/-- The array-store state relation: three concrete names — `arrName` (a
    `.memref n` slot), `idxName` and `srcName` (`.sword 64` words) — are tied to
    the abstract `AArr n` through `wEnc`, pointwise on the array. The array
    analogue of `SRword` (which ties every name to its `wEnc`-encoding). -/
def SRarr (n : Nat) (arrName idxName srcName : String)
    (env : SEnvScalar) (a : AArr n) : Prop :=
  (∃ av : Fin n → BitVec 64,
      env arrName = some ⟨.memref n, av⟩ ∧ ∀ j, wEnc (av j) = a.arr j) ∧
  (∃ iv : BitVec 64, env idxName = some ⟨.sword 64, iv⟩ ∧ iv.toNat = a.idx) ∧
  (∃ sv : BitVec 64, env srcName = some ⟨.sword 64, sv⟩ ∧ wEnc sv = a.src)

/-! ## Dependent-cast helper -/

/-- The `RArrStore` semantics stores `h.symm ▸ memSetDyn …` at type `encodeTy dty`;
    when `dty` encodes to `.memref n` the cast collapses. -/
theorem sigma_memref {n : Nat} {dt : CryptoTy} (h : dt = .memref n)
    (X : Fin n → BitVec 64) :
    (⟨dt, h.symm ▸ X⟩ : (t : CryptoTy) × ⟦t⟧) = ⟨.memref n, X⟩ := by
  cases h; rfl

/-! ## The value leaf -/

/-- **`corres_arrStore`.** The `Corres` value leaf for the dynamic-index array
    write `RArrStore arr idxVar src`. From a concrete `SEnvScalar` related by
    `SRarr` to an abstract `AArr`, running the store under the real `semScalar`
    lands in a state related to the abstract array-update `arr[idx] := src`
    (the `arr` component updated via `memSetDynAbs`). The array analogue of
    `corres_setScalar`. The side conditions: the destination encodes to a
    `.memref n` (`harr`), and the array slot is distinct from the index and
    source slots (`hne_idx`/`hne_src`), so the store preserves them. -/
theorem corres_arrStore {n : Nat} (arr src : Located) (idxVar : String)
    (harr : encodeTy arr.locSrc = .memref n)
    (hne_idx : arr.locVar ≠ idxVar) (hne_src : arr.locVar ≠ src.locVar) :
    Corres (SRarr n arr.locVar idxVar src.locVar) (fun _ => True)
      (fun a => { a with arr := memSetDynAbs a.arr a.idx a.src })
      (.RArrStore arr idxVar src) := by
  intro env a hSR _
  obtain ⟨⟨av, hArr, hArrEnc⟩, ⟨iv, hIdx, hIdxEnc⟩, ⟨sv, hSrc, hSrcEnc⟩⟩ := hSR
  refine ⟨env.upd arr.locVar (t := encodeTy arr.locSrc)
      (harr.symm ▸ memSetDyn av iv.toNat sv), ?_, ?_⟩
  · -- semScalar reduces along the three known lookups + the `harr` guard.
    simp only [semScalar, hArr, hIdx, hSrc, harr, dif_pos]
  · -- the post-state is `SRarr`-related to the abstract array update.
    refine ⟨⟨memSetDyn av iv.toNat sv, ?_, ?_⟩, ⟨iv, ?_, hIdxEnc⟩, ⟨sv, ?_, hSrcEnc⟩⟩
    · -- env' at the array slot holds the concrete store (cast collapsed).
      simp only [SEnvScalar.upd, if_true]
      exact congrArg some (sigma_memref harr (memSetDyn av iv.toNat sv))
    · -- pointwise: encoding of the concrete store = abstract update.
      intro j
      show wEnc (memSetDyn av iv.toNat sv j) = _
      rw [wEnc_memSetDyn av a.arr hArrEnc iv.toNat sv j, hIdxEnc, hSrcEnc]
    · -- index slot preserved (distinct from the array slot).
      simp only [SEnvScalar.upd, if_neg (Ne.symm hne_idx), hIdx]
    · -- source slot preserved (distinct from the array slot).
      simp only [SEnvScalar.upd, if_neg (Ne.symm hne_src), hSrc]

end CatCrypt.Crypto.SecureCompilation.Ascent
