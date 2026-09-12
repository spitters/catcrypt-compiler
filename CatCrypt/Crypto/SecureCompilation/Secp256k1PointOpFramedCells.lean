/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedValue
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpWholeBody

/-!
# The frame-slot value invariant of the secp256k1 doubling body

`Secp256k1PointOpFrontFramed.jacDblBodyFramed` re-tiles the `dbl-2009-l` doubling
body so every field element lives in a slot of a single memref frame `F` (slot
`s` occupies cells `4·s … 4·s+3`). This module carries the memref-state analogue
of the SSA-name value flow behind
`Secp256k1PointOpWholeBody.jacDblBody_cells`: a frame slot holds the little-endian
`u64` value of its four cells, and one frame-relative brick reads its two operand
slots, runs a brick body, and writes the output slot, moving the slot's value by
one base-field operation.

The store half of the tiling (`storeFieldTo`) is the array-name-general
counterpart of `Secp256k1PointOpEpilogue.storeField_cells`; the load half reuses
`Secp256k1PointOpFrameRoundTrip.feVal_of_loadField` at the frame pointer.

## Main results

* `slotVal` — the little-endian `u64` value of a frame slot's four cells.
* `foldl_memSetDyn_hitN`, `foldl_memSetDyn_missN` — the four-cell write window of
  one `storeFieldTo`, over an arbitrary memref length.
* `storeFieldTo_cells` — one `storeFieldTo fw arr o fe`: the frame `arr` ends
  holding an array whose cells `o … o+3` are the four little-endian `u64` limbs
  of `feVal env fe`, and whose other cells are unchanged.
* `slotVal_store_hit`, `slotVal_store_miss` — the store's effect read back as
  `slotVal`: the output slot holds `feVal env fe`, the other slots keep their
  values.
* `loadFieldF_feVal` — a frame load reads the slot value into the loaded field
  element's half-limb readout.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedCells

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr Located TowerType)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll sv mask32)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (storeField limbs4 pointCells feH loadField)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote (feVal)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
  (feHN feHN_eq ofNat_toNat)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (semScalar_recombineStoreList feVal_of_loadField slot_ne_tag head_ne_slot head_ne
   ix_toList)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpEpilogue
  (memSetDyn_at cellWord_toNat feVal_of_reads limbs4_of_halves)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered (HeadOk notTmp_of_len)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed (storeFieldTo)

/-! ## 1. The value a frame slot's four cells carry -/

/-- The little-endian `u64` value of frame slot `s` — cells `4·s … 4·s+3`. -/
def slotVal {N : Nat} (a : Fin N → BitVec 64) (s : Nat) : Nat :=
  (memGetDyn a (4 * s)).toNat + 2 ^ 64 * (memGetDyn a (4 * s + 1)).toNat
    + 2 ^ 128 * (memGetDyn a (4 * s + 2)).toNat + 2 ^ 192 * (memGetDyn a (4 * s + 3)).toNat

/-! ## 2. The four-cell write window over an arbitrary memref length -/

/-- The four-cell write window of one `storeFieldTo`, at a written cell. -/
theorem foldl_memSetDyn_hitN {N : Nat} (b : Fin N → BitVec 64) (o : Nat)
    (V : Nat → BitVec 64) (ho : o + 4 ≤ N) (hcap : N ≤ 2 ^ 64)
    (j : Nat) (hj : j < 4) (m : Fin N) (hm : m.val = o + j) :
    ((List.range 4).foldl
        (fun arr i => memSetDyn arr (BitVec.ofNat 64 (o + i)).toNat (V i)) b) m = V j := by
  have e0 : (BitVec.ofNat 64 (o + 0)).toNat = o + 0 := ofNat_toNat (by omega)
  have e1 : (BitVec.ofNat 64 (o + 1)).toNat = o + 1 := ofNat_toNat (by omega)
  have e2 : (BitVec.ofNat 64 (o + 2)).toNat = o + 2 := ofNat_toNat (by omega)
  have e3 : (BitVec.ofNat 64 (o + 3)).toNat = o + 3 := ofNat_toNat (by omega)
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.foldl_cons, List.foldl_nil,
    e0, e1, e2, e3]
  rw [memSetDyn_at _ _ _ (by omega), memSetDyn_at _ _ _ (by omega),
    memSetDyn_at _ _ _ (by omega), memSetDyn_at _ _ _ (by omega)]
  interval_cases j <;> split_ifs <;> first | rfl | omega

/-- The four-cell write window of one `storeFieldTo`, at a cell outside it. -/
theorem foldl_memSetDyn_missN {N : Nat} (b : Fin N → BitVec 64) (o : Nat)
    (V : Nat → BitVec 64) (ho : o + 4 ≤ N) (hcap : N ≤ 2 ^ 64)
    (m : Fin N) (hm : m.val < o ∨ o + 4 ≤ m.val) :
    ((List.range 4).foldl
        (fun arr i => memSetDyn arr (BitVec.ofNat 64 (o + i)).toNat (V i)) b) m = b m := by
  have e0 : (BitVec.ofNat 64 (o + 0)).toNat = o + 0 := ofNat_toNat (by omega)
  have e1 : (BitVec.ofNat 64 (o + 1)).toNat = o + 1 := ofNat_toNat (by omega)
  have e2 : (BitVec.ofNat 64 (o + 2)).toNat = o + 2 := ofNat_toNat (by omega)
  have e3 : (BitVec.ofNat 64 (o + 3)).toNat = o + 3 := ofNat_toNat (by omega)
  simp only [show List.range 4 = [0, 1, 2, 3] from rfl, List.foldl_cons, List.foldl_nil,
    e0, e1, e2, e3]
  rw [memSetDyn_at _ _ _ (by omega), memSetDyn_at _ _ _ (by omega),
    memSetDyn_at _ _ _ (by omega), memSetDyn_at _ _ _ (by omega)]
  split_ifs <;> first | rfl | omega

/-! ## 3. One `storeFieldTo`, as four frame cells -/

/-- **One `storeFieldTo fw arr o fe`, as a value statement on the frame `arr`.**
    The array-name-general counterpart of
    `Secp256k1PointOpEpilogue.storeField_cells`: from an environment whose eight
    `fe` half-limb slots are bound below `2 ^ 32` and whose index slots
    `ix{o} … ix{o+3}` carry their own numbers, the frame `arr` ends holding an
    array whose cells `o … o+3` are the four little-endian `u64` limbs of
    `feVal env fe`, and whose remaining cells are the incoming ones. -/
theorem storeFieldTo_cells {fw o : Nat} {arr fe : String} {cf ca : Char} {rf ra : List Char}
    {b : Fin ((fw + 7) / 8) → BitVec 64} {env : SEnvScalar}
    (hfe : fe.toList = cf :: rf) (hcf : cf ≠ '_') (hci : cf ≠ 'i')
    (harr : arr.toList = ca :: ra) (hca : ca ≠ cf) (hcaTmp : ¬ isTmpName arr) (hcai : ca ≠ 'i')
    (ho4 : o + 4 ≤ (fw + 7) / 8) (hcap : (fw + 7) / 8 ≤ 2 ^ 64)
    (hb : env arr = some ⟨.memref ((fw + 7) / 8), b⟩)
    (hix : ∀ j, j < 4 → env s!"ix{o + j}" = some ⟨.sword 64, BitVec.ofNat 64 (o + j)⟩)
    (hbnd : ∀ k, k < 8 → env (feHN fe k) = some ⟨.sword 64, envReader env (feHN fe k)⟩)
    (hlt : ∀ k, k < 8 → (envReader env (feHN fe k)).toNat < 2 ^ 32) :
    ∃ (env' : SEnvScalar) (fr : Fin ((fw + 7) / 8) → BitVec 64),
      semScalar (seqAll (storeFieldTo fw arr o fe)) env = some env'
        ∧ env' arr = some ⟨.memref ((fw + 7) / 8), fr⟩
        ∧ (∀ (j : Nat), j < 4 → ∀ (m : Fin ((fw + 7) / 8)), m.val = o + j →
            (fr m).toNat = (limbs4 (feVal env fe)).getD j 0)
        ∧ (∀ (m : Fin ((fw + 7) / 8)), m.val < o ∨ o + 4 ≤ m.val → fr m = b m) := by
  have hfeHead : HeadOk fe := ⟨cf, rf, hfe, hcf⟩
  have hixHead : HeadOk "ix" := ⟨'i', ['x'], rfl, by decide⟩
  have hhT : ∀ k : Nat, ¬ isTmpName s!"{fe}h{k}" :=
    fun _ => HeadOk.notTmp (HeadOk.append (HeadOk.append hfeHead _) _)
  have hgT : ∀ j : Nat, ¬ isTmpName s!"ix{o + j}" :=
    fun _ => HeadOk.notTmp (HeadOk.append hixHead _)
  have hout : ∀ j : Nat, arr ≠ s!"{fe}o{j}" := fun _ => head_ne_slot harr hfe hca
  have hho : ∀ k j : Nat, s!"{fe}h{k}" ≠ s!"{fe}o{j}" :=
    fun _ _ => slot_ne_tag rfl rfl (by decide)
  have hgo : ∀ j j' : Nat, s!"ix{o + j}" ≠ s!"{fe}o{j'}" :=
    fun j _ => head_ne_slot (ix_toList (o + j)) hfe (Ne.symm hci)
  have hhOut : ∀ k : Nat, s!"{fe}h{k}" ≠ arr := fun _ => Ne.symm (head_ne_slot harr hfe hca)
  have hgOut : ∀ j : Nat, s!"ix{o + j}" ≠ arr :=
    fun j => head_ne (ix_toList (o + j)) harr (Ne.symm hcai)
  obtain ⟨env', hs, hfin⟩ :=
    semScalar_recombineStoreList (fw := fw) (outN := arr)
      (iw := fun j => BitVec.ofNat 64 (o + j))
      (A := fun j => envReader env (feHN fe (2 * j)))
      (B := fun j => envReader env (feHN fe (2 * j + 1)))
      (hN := fun k => s!"{fe}h{k}") (oN := fun j => s!"{fe}o{j}") (gN := fun j => s!"ix{o + j}")
      hcaTmp hhT hgT hout hho hgo hhOut hgOut (List.range 4) b env hb
      (fun j hj => hix j (List.mem_range.mp hj))
      (fun j hj => hbnd (2 * j) (by have := List.mem_range.mp hj; omega))
      (fun j hj => hbnd (2 * j + 1) (by have := List.mem_range.mp hj; omega))
  refine ⟨env',
    (List.range 4).foldl (fun arr' i => memSetDyn arr' (BitVec.ofNat 64 (o + i)).toNat
      (envReader env (feHN fe (2 * i))
        + envReader env (feHN fe (2 * i + 1)) <<< (BitVec.ofNat 64 32).toNat)) b,
    hs, hfin, ?_, ?_⟩
  · intro j hj m hm
    rw [foldl_memSetDyn_hitN b o
        (fun i => envReader env (feHN fe (2 * i))
          + envReader env (feHN fe (2 * i + 1)) <<< (BitVec.ofNat 64 32).toNat)
        ho4 hcap j hj m hm,
      cellWord_toNat (hlt (2 * j) (by omega)) (hlt (2 * j + 1) (by omega)),
      feVal_of_reads env fe (fun k => (envReader env (feHN fe k)).toNat) (fun _ _ => rfl),
      limbs4_of_halves _ _ _ _ _ _ _ _
        (hlt 0 (by norm_num)) (hlt 1 (by norm_num)) (hlt 2 (by norm_num))
        (hlt 3 (by norm_num)) (hlt 4 (by norm_num)) (hlt 5 (by norm_num))
        (hlt 6 (by norm_num)) (hlt 7 (by norm_num))]
    interval_cases j <;> norm_num
  · intro m hm
    exact foldl_memSetDyn_missN b o _ ho4 hcap m hm

/-! ## 4. Reading the store back as `slotVal` -/

/-- An in-range dynamic read hits the plain index. -/
theorem memGetDyn_lt {N : Nat} (a : Fin N → BitVec 64) {k : Nat} (hk : k < N) :
    memGetDyn a k = a ⟨k, hk⟩ := by
  match N, a with
  | 0, _ => exact absurd hk (Nat.not_lt_zero k)
  | (m + 1), a => simp only [memGetDyn, Nat.mod_eq_of_lt hk]

/-- **The written slot holds the stored value.** Reading back the four cells one
    `storeFieldTo` writes into slot `s` recovers a canonical residue. -/
theorem slotVal_hit {N : Nat} (fr : Fin N → BitVec 64) (s v : Nat)
    (hv : v < 2 ^ 256) (hs : 4 * s + 4 ≤ N)
    (hit : ∀ (j : Nat), j < 4 → ∀ (m : Fin N), m.val = 4 * s + j →
        (fr m).toNat = (limbs4 v).getD j 0) :
    slotVal fr s = v := by
  have h0 : (memGetDyn fr (4 * s)).toNat = v % 2 ^ 64 := by
    rw [memGetDyn_lt fr (by omega : 4 * s < N), hit 0 (by norm_num) ⟨4 * s, by omega⟩ rfl]
    simp [limbs4]
  have h1 : (memGetDyn fr (4 * s + 1)).toNat = v / 2 ^ 64 % 2 ^ 64 := by
    rw [memGetDyn_lt fr (by omega : 4 * s + 1 < N), hit 1 (by norm_num) ⟨4 * s + 1, by omega⟩ rfl]
    simp [limbs4]
  have h2 : (memGetDyn fr (4 * s + 2)).toNat = v / 2 ^ 128 % 2 ^ 64 := by
    rw [memGetDyn_lt fr (by omega : 4 * s + 2 < N), hit 2 (by norm_num) ⟨4 * s + 2, by omega⟩ rfl]
    simp [limbs4]
  have h3 : (memGetDyn fr (4 * s + 3)).toNat = v / 2 ^ 192 % 2 ^ 64 := by
    rw [memGetDyn_lt fr (by omega : 4 * s + 3 < N), hit 3 (by norm_num) ⟨4 * s + 3, by omega⟩ rfl]
    simp [limbs4]
  simp only [slotVal, h0, h1, h2, h3]
  omega

/-- **A slot other than the written one keeps its value.** -/
theorem slotVal_miss {N : Nat} (fr b : Fin N → BitVec 64) (s s' : Nat)
    (hs' : 4 * s' + 4 ≤ N) (hne : s' ≠ s)
    (miss : ∀ (m : Fin N), m.val < 4 * s ∨ 4 * s + 4 ≤ m.val → fr m = b m) :
    slotVal fr s' = slotVal b s' := by
  have h0 : memGetDyn fr (4 * s') = memGetDyn b (4 * s') := by
    rw [memGetDyn_lt fr (by omega : 4 * s' < N), memGetDyn_lt b (by omega : 4 * s' < N),
      miss ⟨4 * s', by omega⟩ (by show 4 * s' < 4 * s ∨ 4 * s + 4 ≤ 4 * s'; omega)]
  have h1 : memGetDyn fr (4 * s' + 1) = memGetDyn b (4 * s' + 1) := by
    rw [memGetDyn_lt fr (by omega : 4 * s' + 1 < N), memGetDyn_lt b (by omega : 4 * s' + 1 < N),
      miss ⟨4 * s' + 1, by omega⟩ (by show 4 * s' + 1 < 4 * s ∨ 4 * s + 4 ≤ 4 * s' + 1; omega)]
  have h2 : memGetDyn fr (4 * s' + 2) = memGetDyn b (4 * s' + 2) := by
    rw [memGetDyn_lt fr (by omega : 4 * s' + 2 < N), memGetDyn_lt b (by omega : 4 * s' + 2 < N),
      miss ⟨4 * s' + 2, by omega⟩ (by show 4 * s' + 2 < 4 * s ∨ 4 * s + 4 ≤ 4 * s' + 2; omega)]
  have h3 : memGetDyn fr (4 * s' + 3) = memGetDyn b (4 * s' + 3) := by
    rw [memGetDyn_lt fr (by omega : 4 * s' + 3 < N), memGetDyn_lt b (by omega : 4 * s' + 3 < N),
      miss ⟨4 * s' + 3, by omega⟩ (by show 4 * s' + 3 < 4 * s ∨ 4 * s + 4 ≤ 4 * s' + 3; omega)]
  simp only [slotVal, h0, h1, h2, h3]

/-! ## 5. Reading a frame load as `slotVal` -/

/-- **A frame load reads the slot value.** Loading slot `s` of the frame `arr`
    into `fe` leaves `fe`'s half-limb residue readout equal to `slotVal a s`. -/
theorem loadFieldF_slotVal {fw s N : Nat} {arr fe : String} {cf ca : Char}
    {rf ra : List Char} {a : Fin N → BitVec 64} {env : SEnvScalar}
    (hfe : fe.toList = cf :: rf) (hcf : cf ≠ '_') (hci : cf ≠ 'i')
    (harr : arr.toList = ca :: ra) (hca : ca ≠ cf) (hcap : 4 * s + 4 ≤ 2 ^ 64)
    (ha : env arr = some ⟨.memref N, a⟩)
    (hix : ∀ j, j < 4 → env s!"ix{4 * s + j}" = some ⟨.sword 64, BitVec.ofNat 64 (4 * s + j)⟩) :
    ∃ env', semScalar (seqAll (loadField fw arr (4 * s) fe)) env = some env'
      ∧ feVal env' fe = slotVal a s := by
  obtain ⟨env', hs, hv⟩ :=
    feVal_of_loadField (fw := fw) (o := 4 * s) (iw := fun j => BitVec.ofNat 64 (4 * s + j))
      hfe hcf hci harr hca ha hix
  refine ⟨env', hs, ?_⟩
  have e0 : (BitVec.ofNat 64 (4 * s)).toNat = 4 * s := ofNat_toNat (by omega)
  have e1 : (BitVec.ofNat 64 (4 * s + 1)).toNat = 4 * s + 1 := ofNat_toNat (by omega)
  have e2 : (BitVec.ofNat 64 (4 * s + 2)).toNat = 4 * s + 2 := ofNat_toNat (by omega)
  have e3 : (BitVec.ofNat 64 (4 * s + 3)).toNat = 4 * s + 3 := ofNat_toNat (by omega)
  rw [hv]
  simp only [slotVal, Nat.add_zero, e0, e1, e2, e3]

/-! ## 6. The frame-slot value invariant -/

/-- **The frame-slot value invariant.** The first `active` slots of the frame `a`
    hold the canonical residues `V 0, …, V (active-1)`. -/
def FrameSlots {N : Nat} (a : Fin N → BitVec 64) (V : Nat → Nat) (active : Nat) : Prop :=
  ∀ s, s < active → slotVal a s = V s

/-- **The frame-slot invariant is preserved by one `storeFieldTo`.** Storing a
    field element holding the canonical residue `feVal env fe` into slot `so`
    updates the frame so the invariant holds for the valuation with slot `so`
    reset to that residue. The other slots keep their values; slot `so` takes the
    stored one. -/
theorem frameSlots_store {fw so : Nat} {arr fe : String} {cf ca : Char} {rf ra : List Char}
    {b : Fin ((fw + 7) / 8) → BitVec 64} {env : SEnvScalar} {V : Nat → Nat} {active : Nat}
    (hfe : fe.toList = cf :: rf) (hcf : cf ≠ '_') (hci : cf ≠ 'i')
    (harr : arr.toList = ca :: ra) (hca : ca ≠ cf) (hcaTmp : ¬ isTmpName arr) (hcai : ca ≠ 'i')
    (hso4 : 4 * so + 4 ≤ (fw + 7) / 8) (hcap : (fw + 7) / 8 ≤ 2 ^ 64)
    (hactive : ∀ s, s < active → 4 * s + 4 ≤ (fw + 7) / 8)
    (hb : env arr = some ⟨.memref ((fw + 7) / 8), b⟩)
    (hix : ∀ j, j < 4 → env s!"ix{4 * so + j}" = some ⟨.sword 64, BitVec.ofNat 64 (4 * so + j)⟩)
    (hbnd : ∀ k, k < 8 → env (feHN fe k) = some ⟨.sword 64, envReader env (feHN fe k)⟩)
    (hlt : ∀ k, k < 8 → (envReader env (feHN fe k)).toNat < 2 ^ 32)
    (hvlt : feVal env fe < 2 ^ 256)
    (hInv : FrameSlots b V active) :
    ∃ (env' : SEnvScalar) (fr : Fin ((fw + 7) / 8) → BitVec 64),
      semScalar (seqAll (storeFieldTo fw arr (4 * so) fe)) env = some env'
        ∧ env' arr = some ⟨.memref ((fw + 7) / 8), fr⟩
        ∧ FrameSlots fr (Function.update V so (feVal env fe)) active := by
  obtain ⟨env', fr, hs, hbfr, hhit, hmiss⟩ :=
    storeFieldTo_cells hfe hcf hci harr hca hcaTmp hcai hso4 hcap hb hix hbnd hlt
  refine ⟨env', fr, hs, hbfr, ?_⟩
  intro s hsa
  by_cases hso : s = so
  · subst hso
    rw [Function.update_self,
      slotVal_hit fr s (feVal env fe) hvlt hso4 (fun j hj m hm => hhit j hj m hm)]
  · rw [Function.update_of_ne hso, ← hInv s hsa,
      slotVal_miss fr b so s (hactive s hsa) hso (fun m hm => hmiss m hm)]

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedCells
