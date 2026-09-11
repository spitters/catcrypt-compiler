/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.TowerLimbStore

/-!
# Component load on tower tuple values

`LowCT.RTupleLoad dst src idx` reads component `idx` of the tuple value at
`src` into `dst`, and `RustExec.tupleLoad` routes that read through the
`LeafSpec.tupleLoad` oracle.  This module supplies the oracle's value:
`towerTupleLoad` copies the component's byte window out of the source and
`concreteTupleLoad` packages it as a `TupleLoadSpec`.

A tower value is a byte array (`RustVal t = JArray t.storageBytes`), and
`TowerType.tupleComponentByteOffset` / `tupleComponentByteSize` fix where a
component sits inside `TTuple a b`: component 0 at offset 0 for
`a.storageBytes` bytes, component 1 at offset `a.storageBytes` for
`b.storageBytes`.  The load reads that window and zero-fills the rest of the
destination, so it is total: a non-`TTuple` source has component size 0 and
loads as zero, and a destination wider than the component keeps no stale
bytes.  Zero-fill rather than preserving the old destination is what makes
this a load and not a partial write.

## Main results

* `towerTupleLoad` / `concreteTupleLoad` — the component read and the
  `LeafSpec` field that uses it.
* `rustValByte_towerTupleLoad_inside` — inside the component width, the
  destination byte is the source byte at the component's offset.
* `rustValByte_towerTupleLoad_outside` — past the component width, zero.
* `towerTupleLoad_fst` / `towerTupleLoad_snd` — on a `TTuple a b` source the
  two components read back at their own offsets.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCT

/-- Read component `idx` of the tuple value `src` into a value of type `dstT`:
    the bytes at `src`'s component offset, for the component's width, and zero
    past it. -/
def towerTupleLoad {dstT : TowerType} (src : Σ t : TowerType, RustVal t)
    (idx : Nat) : RustVal dstT :=
  fun j =>
    if j.val < src.1.tupleComponentByteSize idx then
      rustValByte src.2 (src.1.tupleComponentByteOffset idx + j.val)
    else 0

/-- Inside the component's width, the loaded byte is the source byte at the
    component's offset. -/
theorem rustValByte_towerTupleLoad_inside {dstT : TowerType}
    (src : Σ t : TowerType, RustVal t) (idx k : Nat)
    (hk : k < dstT.storageBytes)
    (hsz : k < src.1.tupleComponentByteSize idx) :
    rustValByte (towerTupleLoad (dstT := dstT) src idx) k =
      rustValByte src.2 (src.1.tupleComponentByteOffset idx + k) := by
  simp only [rustValByte, towerTupleLoad, dif_pos hk]
  rw [if_pos hsz]

/-- Past the component's width, the loaded byte is zero. -/
theorem rustValByte_towerTupleLoad_outside {dstT : TowerType}
    (src : Σ t : TowerType, RustVal t) (idx k : Nat)
    (hsz : ¬ k < src.1.tupleComponentByteSize idx) :
    rustValByte (towerTupleLoad (dstT := dstT) src idx) k = 0 := by
  simp [rustValByte, towerTupleLoad, hsz]

/-- Component 0 of a `TTuple a b` source reads from offset 0. -/
theorem towerTupleLoad_fst {dstT a b : TowerType} (v : RustVal (.TTuple a b))
    (k : Nat) (hk : k < dstT.storageBytes) (hsz : k < a.storageBytes) :
    rustValByte (towerTupleLoad (dstT := dstT) ⟨.TTuple a b, v⟩ 0) k =
      rustValByte v k := by
  rw [rustValByte_towerTupleLoad_inside _ 0 k hk (by simpa using! hsz)]
  simp [TowerType.tupleComponentByteOffset]

/-- Component 1 of a `TTuple a b` source reads from offset `a.storageBytes`. -/
theorem towerTupleLoad_snd {dstT a b : TowerType} (v : RustVal (.TTuple a b))
    (k : Nat) (hk : k < dstT.storageBytes) (hsz : k < b.storageBytes) :
    rustValByte (towerTupleLoad (dstT := dstT) ⟨.TTuple a b, v⟩ 1) k =
      rustValByte v (a.storageBytes + k) := by
  rw [rustValByte_towerTupleLoad_inside _ 1 k hk (by simpa using! hsz)]
  rfl

/-- The tuple-load oracle: `RTupleLoad dst src idx` sets the value at `dst` to
    component `idx` of the value at `src`. -/
def concreteTupleLoad : TupleLoadSpec :=
  fun _dst _oldV src idx => towerTupleLoad src idx

end CatCrypt.Crypto.Jasmin.LowCT
