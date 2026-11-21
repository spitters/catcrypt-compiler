/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomLoadsK
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomAssemble

/-!
# Known indices through the back half of the region gate

The fold positions `FoldPos` of the cell fold check `regionFoldB` ask, at every array access of the
code behind the prefix of the parts, that the index register holds a known constant (`KnownAt`). The
export of a program of the shape `LoadsChainK` has this property (`IdxKnown`,
`loadsChainK_export_knownAt`). The back half of the gate reaches the code of `FoldPos` from
the export through position-preserving maps (the webs and the coalescing rename array
positions, the pairs and the merge rename names, `selfNop` replaces instructions in place),
appended copies (`movesOf`, `resCopyCode`) and the expansion `fuseMulHiRM` of the
multiplication sites (`expI`). Each of these keeps `IdxKnown` under a condition on the names
it writes.

## Main definitions

* `IdxKnown`: at every array access of a code the index register holds a known constant
  below the length of the array.
* `PosClass`: an instruction is an access of a cell array of the right length, or is kept
  by the fold.

## Main results

* `knownAt_of_getElem?`, `idxKnown_of_getElem?`: transport along a position-preserving map.
* `idxKnown_append`, `idxKnown_resCopyCode`, `idxKnown_movesOf`: appended code.
* `idxKnown_map_renArr`, `idxKnown_map_renRM`: renamings of array positions and of names.
* `idxKnown_mapIdx_selfNopI`, `idxKnown_selfNop_drop`: the replacement of array self-moves by
  self moves of their index registers.
* `knownAt_expI`, `idxKnown_expI`: expansions by position.
* `foldPos_of_posClass`, `foldPos_of_idxKnown`: the fold positions from `IdxKnown` and
  `PosClass`.
* `idxKnown_regionWebs`, `idxKnown_regionCoParts`: the webs and the parts keep `IdxKnown`.
* `fieldBody_idxKnown`, `fieldDom_renOf_ps`: on the field domain, the webs of the export have
  known indices, and the pairs send no other name to an access index.
* `fieldDom_foldPos_of_back`: the field `foldPos` of `FieldDomOpen` from the shape
  `LoadsChainK` of the legalized chain output, the coalescing renaming at the access indices,
  at fusion sites the absence of array self-moves and the names of the sites, and the fold
  class of the code behind the prefix.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renLinstrR
  renOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr renLoad renStore
  renZero renStoreImm renCallW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots isArrB isCellB lenOf
  keepB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldL (ctlB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CellFoldLReg (keepRegB)

/-! ## 1. Known indices -/

/-- **At every array access of the code `C` the index register holds a known constant below
    the length of the array.** -/
def IdxKnown (C : List LinstrRM) : Prop :=
  ∀ (k : Nat) (ins : LinstrRM) (x : String) (m : Nat), C[k]? = some ins → AccIdx ins x m →
    ∃ c < m, KnownAt C k x c

/-- **A known constant along a position-preserving map** `g`: the move of the constant into
    `x` is sent to the move into `x'`, the self move of `x` to the self move of `x'`, and an
    operation that does not write `x` to an operation that does not write `x'` or to the self
    move of `x'`. -/
theorem knownAt_of_getElem? {C C' : List LinstrRM} (g : Nat → LinstrRM → LinstrRM)
    (hC : ∀ j, C'[j]? = (C[j]?).map (g j)) {k : Nat} {x x' : String} {c : Nat}
    (hmov : ∀ j < k, g j (.Lopn [.reg x] "MOV:64" [.imm c], .reg none)
      = (.Lopn [.reg x'] "MOV:64" [.imm c], .reg none))
    (hself : ∀ j < k, g j (selfMovI x) = selfMovI x')
    (hop : ∀ j < k, ∀ i, C[j]? = some i → (∃ ds o ss, i.1 = .Lopn ds o ss) →
      x ∉ dstNames i.1 → (∃ ds o ss, (g j i).1 = .Lopn ds o ss) ∧
        (x' ∉ dstNames (g j i).1 ∨ g j i = selfMovI x'))
    (h : KnownAt C k x c) : KnownAt C' k x' c := by
  obtain ⟨j, hj, hJ, hmid⟩ := h
  refine ⟨j, hj, by rw [hC, hJ, Option.map_some, hmov j hj], fun j' h1 h2 i hi => ?_⟩
  rw [hC] at hi
  obtain ⟨i0, hi0, rfl⟩ := Option.map_eq_some_iff.mp hi
  obtain ⟨hl, hn | rfl⟩ := hmid j' h1 h2 i0 hi0
  · exact hop j' (by omega) i0 hi0 hl hn
  · rw [hself j' (by omega)]
    exact ⟨⟨_, _, _, rfl⟩, .inr rfl⟩

/-- **Known indices along a position-preserving map** `g`: every access of the image comes
    from an access of the same length whose index `f` sends to the new index, and the known
    constant of each access index is carried. -/
theorem idxKnown_of_getElem? {C C' : List LinstrRM} (g : Nat → LinstrRM → LinstrRM)
    (hC : ∀ j, C'[j]? = (C[j]?).map (g j)) (f : String → String)
    (hacc : ∀ j i x m, C[j]? = some i → AccIdx (g j i) x m → ∃ x0, x = f x0 ∧ AccIdx i x0 m)
    (hK : ∀ k i x0 m c, C[k]? = some i → AccIdx i x0 m → KnownAt C k x0 c →
      KnownAt C' k (f x0) c)
    (h : IdxKnown C) : IdxKnown C' := by
  intro k ins x m hk hacc'
  rw [hC] at hk
  obtain ⟨i0, hi0, rfl⟩ := Option.map_eq_some_iff.mp hk
  obtain ⟨x0, rfl, ha⟩ := hacc k i0 x m hi0 hacc'
  obtain ⟨c, hc, hkn⟩ := h k i0 x0 m hi0 ha
  exact ⟨c, hc, hK k i0 x0 m c hi0 ha hkn⟩

/-! ## 2. Appended code -/

/-- A known constant of a code is known in the code with a code appended. -/
theorem knownAt_append_left {C D : List LinstrRM} {k : Nat} {x : String} {c : Nat}
    (hk : k ≤ C.length) (h : KnownAt C k x c) : KnownAt (C ++ D) k x c := by
  obtain ⟨j, hj, hJ, hmid⟩ := h
  refine ⟨j, hj, by rw [List.getElem?_append_left (by omega)]; exact hJ,
    fun j' h1 h2 i hi => hmid j' h1 h2 i ?_⟩
  rwa [List.getElem?_append_left (by omega)] at hi

/-- A known constant of a code is known in the code behind a prefix. -/
theorem knownAt_append_right {C D : List LinstrRM} {k : Nat} {x : String} {c : Nat}
    (h : KnownAt D k x c) : KnownAt (C ++ D) (C.length + k) x c := by
  obtain ⟨j, hj, hJ, hmid⟩ := h
  refine ⟨C.length + j, by omega, by rw [List.getElem?_append_right (by omega)]; simpa using hJ,
    fun j' h1 h2 i hi => hmid (j' - C.length) (by omega) (by omega) i ?_⟩
  rwa [List.getElem?_append_right (by omega)] at hi

/-- **Known indices of an appended code.** -/
theorem idxKnown_append {C D : List LinstrRM} (hC : IdxKnown C) (hD : IdxKnown D) :
    IdxKnown (C ++ D) := by
  intro k ins x m hk hacc
  by_cases hlt : k < C.length
  · rw [List.getElem?_append_left hlt] at hk
    obtain ⟨c, hc, h⟩ := hC k ins x m hk hacc
    exact ⟨c, hc, knownAt_append_left (by omega) h⟩
  · rw [List.getElem?_append_right (by omega)] at hk
    obtain ⟨c, hc, h⟩ := hD (k - C.length) ins x m hk hacc
    have h' := knownAt_append_right (C := C) h
    rw [show C.length + (k - C.length) = k by omega] at h'
    exact ⟨c, hc, h'⟩

/-- A code without an array access has known indices. -/
theorem idxKnown_of_noAcc {C : List LinstrRM} (h : ∀ i ∈ C, ∀ x m, ¬ AccIdx i x m) :
    IdxKnown C := fun _ ins x m hk hacc => absurd hacc (h ins (List.mem_of_getElem? hk) x m)

/-- The copies of the pairs have known indices: they access no array. -/
theorem idxKnown_movesOf (ps : List (String × String)) :
    IdxKnown (JasminLsemRenameLoop.movesOf ps) := by
  refine idxKnown_of_noAcc fun i hi x m => ?_
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  exact not_accIdx_reg

/-- **The result copy has known indices**: each word is read and written at the index the
    move in front of it sets. -/
theorem idxKnown_resCopyCode (src D : String) (m : Nat) : IdxKnown (resCopyCode src D m) := by
  intro p ins x m' hp hacc
  have hlt : p < 3 * m := by
    have := (List.getElem?_eq_some_iff.mp hp).1
    rwa [length_resCopyCode] at this
  obtain ⟨j, hj, ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ :=
    resCopyCode_at (src := src) (D := D) (m := m) hlt
  · rw [hp] at h
    cases h
    exact absurd hacc not_accIdx_reg
  · rw [hp] at h
    cases h
    obtain ⟨ds, o, b, s, ss, w, h1, h2 | h2⟩ := hacc
    · simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.arrIdx.injEq] at h1
      simp only [JasminLsemMem.MemTag.load.injEq] at h2
      obtain ⟨-, -, ⟨-, rfl, -⟩, -⟩ := h1
      obtain ⟨-, rfl⟩ := h2
      refine ⟨j, hj, 3 * j, by omega, ?_, fun j' h1 h2 => by omega⟩
      have h0 := getElem?_resCopyCode src D (m := m) (j := j) (i := 0) hj (by omega)
      rw [Nat.add_zero] at h0
      rw [h0]
      rfl
    · cases h2
  · rw [hp] at h
    cases h
    obtain ⟨ds, o, b, s, ss, w, h1, h2 | h2⟩ := hacc
    · cases h2
    · simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.arrIdx.injEq] at h1
      simp only [JasminLsemMem.MemTag.store.injEq] at h2
      obtain ⟨-, -, ⟨-, rfl, -⟩, -⟩ := h1
      obtain ⟨-, rfl⟩ := h2
      refine ⟨j, hj, 3 * j, by omega, ?_, fun j' h1 h2 i hi => ?_⟩
      · have h0 := getElem?_resCopyCode src D (m := m) (j := j) (i := 0) hj (by omega)
        rw [Nat.add_zero] at h0
        rw [h0]
        rfl
      · have hj' : j' = 3 * j + 1 := by omega
        subst hj'
        have h0 := getElem?_resCopyCode src D (m := m) (j := j) (i := 1) hj (by omega)
        rw [h0] at hi
        cases hi
        refine ⟨⟨_, _, _, rfl⟩, .inl ?_⟩
        simp [dstNames, JasminLsemExportRewrites.opNames, copyIdx, copyTmp]

/-! ## 3. Renamings -/

/-- The renaming of the array positions writes the written names or their images. -/
theorem dstNames_renArr (ρ : String → String) (i : LinstrRM) :
    ∀ n ∈ dstNames (renArr ρ i).1, n ∈ dstNames i.1 ∨ ∃ y ∈ dstNames i.1, n = ρ y := by
  intro n hn
  obtain ⟨w, tag⟩ := i
  cases tag <;> simp only [renArr, renLoad, renStore, renZero, renStoreImm, renCallW] at hn <;>
    (repeat' split at hn) <;>
    first
    | (simp_all [dstNames, JasminLsemExportRewrites.opNames]; done)
    | (rename_i hs
       rw [LprogIsa.eq_callShadow_of_shadowCall? hs]
       simp_all [dstNames, JasminLsemExportRewrites.opNames, LprogIsa.callShadow])

/-- The renaming of the array positions keeps the index and the tag of an access. -/
theorem accIdx_of_renArr (ρ : String → String) {i : LinstrRM} {x : String} {m : Nat}
    (h : AccIdx (renArr ρ i) x m) : AccIdx i x m := by
  obtain ⟨ds, o, b, s, ss, w, h1, h2⟩ := h
  obtain ⟨wi, tag⟩ := i
  cases tag <;> simp only [renArr, renLoad, renStore, renZero, renStoreImm, renCallW] at h1 h2 <;>
    (repeat' split at h1) <;> grind [AccIdx]

/-- The renaming of the array positions keeps an operation an operation. -/
theorem lopn_renArr (ρ : String → String) {i : LinstrRM} (h : ∃ ds o ss, i.1 = .Lopn ds o ss) :
    ∃ ds o ss, (renArr ρ i).1 = .Lopn ds o ss :=
  RegionExportDefInitSort.isLopn_renArr ρ h

/-- The renaming of the array positions keeps a self move. -/
theorem renArr_selfMovI (ρ : String → String) (x : String) :
    renArr ρ (selfMovI x) = selfMovI x := by
  simp [selfMovI, renArr, renCallW, LprogIsa.shadowCall?]

/-- **Known indices along a renaming of the array positions** that sends no other name to an
    access index. -/
theorem idxKnown_renArr {C C' : List LinstrRM} (ρ : Nat → LinstrRM → String → String)
    (hC : ∀ j, C'[j]? = (C[j]?).map fun i => renArr (ρ j i) i)
    (hx : ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat), C[k]? = some i → AccIdx i x m →
      ∀ (j : Nat) (i' : LinstrRM) (y : String), ρ j i' y = x → y = x)
    (h : IdxKnown C) : IdxKnown C' := by
  refine idxKnown_of_getElem? (fun j i => renArr (ρ j i) i) hC id
    (fun j i x m _ ha => ⟨x, rfl, accIdx_of_renArr _ ha⟩) ?_ h
  intro k i x0 m c hk ha hK
  refine knownAt_of_getElem? _ hC (fun j _ => RegionExportDefInitSort.renArr_movImmI _ x0 c)
    (fun j _ => renArr_selfMovI _ x0) ?_ hK
  intro j _ i' _ hl hn
  refine ⟨lopn_renArr _ hl, .inl fun hm => ?_⟩
  rcases dstNames_renArr _ i' x0 hm with h1 | ⟨y, hy, he⟩
  · exact hn h1
  · exact hn (hx k i x0 m hk ha j i' y he.symm ▸ hy)

/-- The renaming of names renames the written names. -/
theorem dstNames_renLinstrR (f : String → String) (w : LinstrR) :
    dstNames (renLinstrR f w) = (dstNames w).map f := by
  cases w with
  | Lopn d o s =>
      simp only [renLinstrR, dstNames, List.flatMap_map, List.map_flatMap]
      congr 1
      funext o
      cases o <;> rfl
  | _ => rfl

/-- The renaming of names renames the index of an access. -/
theorem accIdx_of_renRM (f : String → String) {i : LinstrRM} {x : String} {m : Nat}
    (h : AccIdx (renRM f i) x m) : ∃ x0, x = f x0 ∧ AccIdx i x0 m := by
  obtain ⟨ds, o, b, s, ss, w, h1, h2⟩ := h
  obtain ⟨wi, tag⟩ := i
  cases wi with
  | Lopn ds0 o0 ss0 =>
      simp only [renRM, renLinstrR] at h1 h2
      cases ss0 with
      | nil => simp at h1
      | cons a ss0 =>
          cases a with
          | arrIdx b0 x0 s0 =>
              simp only [List.map_cons, renOperand, LinstrR.Lopn.injEq, List.cons.injEq,
                LOperand.arrIdx.injEq] at h1
              obtain ⟨-, rfl, ⟨-, rfl, -⟩, -⟩ := h1
              exact ⟨_, rfl, _, _, _, _, _, w, rfl, h2⟩
          | _ => simp [renOperand] at h1
  | _ => simp [renRM, renLinstrR] at h1

/-- **Known indices along a renaming of names** that is injective at every access index. -/
theorem idxKnown_map_renRM {C : List LinstrRM} (f : String → String)
    (hinj : ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat), C[k]? = some i →
      AccIdx i x m → ∀ y, f y = f x → y = x)
    (h : IdxKnown C) : IdxKnown (C.map (renRM f)) := by
  have hC : ∀ j, (C.map (renRM f))[j]? = (C[j]?).map fun i => renRM f i := fun j =>
    List.getElem?_map
  refine idxKnown_of_getElem? (fun _ i => renRM f i) hC f
    (fun j i x m _ ha => accIdx_of_renRM f ha) ?_ h
  intro k i x0 m c hk ha hK
  refine knownAt_of_getElem? _ hC (fun j _ => rfl) (fun j _ => rfl) ?_ hK
  intro j _ i' _ hl hn
  obtain ⟨ds, o, ss, he⟩ := hl
  refine ⟨⟨_, _, _, by simp only [renRM, he, renLinstrR]; rfl⟩, .inl fun hm => ?_⟩
  simp only [renRM, dstNames_renLinstrR, List.mem_map] at hm
  obtain ⟨y, hy, he'⟩ := hm
  exact hn (hinj k i x0 m hk ha y he' ▸ hy)

/-- Without a pair of an array self-move, `selfNop` keeps the code. -/
theorem selfNop_eq_of_noPair {k0 : Nat} {Lr : Nat → List String} {B : List LinstrRM}
    (h : ∀ k, selfPairB k0 Lr B k = false) : selfNop k0 Lr B = B := by
  apply List.ext_getElem?
  intro k
  simp only [selfNop, List.getElem?_mapIdx, h]
  cases B[k]? <;> simp

/-- The replacement `selfNopI` keeps an instruction or is the self move of a register. -/
theorem selfNopI_eq_or_selfMovI (i : LinstrRM) :
    selfNopI i = i ∨ ∃ z, selfNopI i = selfMovI z := by
  unfold selfNopI
  split
  · exact .inr ⟨_, rfl⟩
  · exact .inl rfl

/-- **Replacing positions by `selfNopI` keeps known indices**, at every choice of positions. -/
theorem idxKnown_mapIdx_selfNopI (P : Nat → Bool) {C : List LinstrRM} (h : IdxKnown C) :
    IdxKnown (C.mapIdx fun k i => if P k then selfNopI i else i) := by
  have hC : ∀ j, (C.mapIdx fun k i => if P k then selfNopI i else i)[j]? =
      (C[j]?).map fun i => if P j then selfNopI i else i := fun j => List.getElem?_mapIdx
  refine idxKnown_of_getElem? (fun j i => if P j then selfNopI i else i) hC id
    (fun j i x m _ ha => ⟨x, rfl, ?_⟩) ?_ h
  · split at ha
    · rcases selfNopI_eq_or_selfMovI i with hs | ⟨z, hs⟩
      · rwa [hs] at ha
      · rw [hs] at ha
        exact absurd ha not_accIdx_reg
    · exact ha
  · intro k i x0 m c _ _ hK
    refine knownAt_of_getElem? _ hC (fun j _ => by split <;> rfl) (fun j _ => by split <;> rfl)
      ?_ hK
    intro j _ i' _ hl hn
    split
    · rcases selfNopI_eq_or_selfMovI i' with hs | ⟨z, hs⟩
      · rw [hs]
        exact ⟨hl, .inl hn⟩
      · rw [hs]
        refine ⟨⟨_, _, _, rfl⟩, ?_⟩
        by_cases hz : z = x0
        · exact .inr (hz ▸ rfl)
        · exact .inl (by simp [selfMovI, dstNames, JasminLsemExportRewrites.opNames, Ne.symm hz])
    · exact ⟨hl, .inl hn⟩

/-- **`selfNop` behind a prefix keeps known indices.** -/
theorem idxKnown_selfNop_drop {A B : List LinstrRM} (Lr : Nat → List String)
    (h : IdxKnown B) : IdxKnown ((selfNop A.length Lr (A ++ B)).drop A.length) := by
  unfold selfNop
  rw [List.mapIdx_append, List.drop_left' (List.length_mapIdx ..)]
  exact idxKnown_mapIdx_selfNopI _ h

/-! ## 4. Expansions by position -/

section Exp

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (expI pcI expI_append pcI_succ
  getElem?_expI_pcI)

variable (e : Nat → LinstrRM → List LinstrRM)

/-- **Every position of an expansion lies in the expansion of one instruction.** -/
theorem getElem?_expI_inv : ∀ (C : List LinstrRM) (n p : Nat) (i' : LinstrRM),
    (expI e C n)[p]? = some i' → ∃ j i r, C[j]? = some i ∧ (e (n + j) i)[r]? = some i' ∧
      p = (expI e (C.take j) n).length + r
  | [], n, p, i', h => by simp [expI] at h
  | i :: is, n, p, i', h => by
      rw [expI] at h
      by_cases hp : p < (e n i).length
      · rw [List.getElem?_append_left hp] at h
        exact ⟨0, i, p, rfl, by simpa using h, by simp [expI]⟩
      · rw [List.getElem?_append_right (by omega)] at h
        obtain ⟨j, i0, r, hj, he, hpe⟩ := getElem?_expI_inv is (n + 1) _ i' h
        refine ⟨j + 1, i0, r, by simpa using hj, ?_, ?_⟩
        · rw [show n + (j + 1) = n + 1 + j by omega]
          exact he
        · rw [List.take_succ_cons, expI, List.length_append]
          omega

/-- The start positions of the expansion grow with the position. -/
theorem pcI_mono (C : List LinstrRM) {j j' : Nat} (h : j ≤ j') : pcI e C j ≤ pcI e C j' := by
  unfold pcI
  have hs := (List.take_append_drop j (C.take j')).symm
  rw [List.take_take, Nat.min_eq_left h] at hs
  rw [hs, expI_append, List.length_append]
  omega

/-- **A known constant through an expansion** that keeps the move of the constant and the
    self move of `x` and expands each operation that does not write `x` into operations that
    do not write `x`. -/
theorem knownAt_expI {C : List LinstrRM} {k : Nat} {x : String} {c : Nat}
    (hmov : ∀ j, e j (.Lopn [.reg x] "MOV:64" [.imm c], .reg none)
      = [(.Lopn [.reg x] "MOV:64" [.imm c], .reg none)])
    (hself : ∀ j, e j (selfMovI x) = [selfMovI x])
    (hop : ∀ j i, C[j]? = some i → (∃ ds o ss, i.1 = .Lopn ds o ss) → x ∉ dstNames i.1 →
      ∀ i' ∈ e j i, (∃ ds o ss, i'.1 = .Lopn ds o ss) ∧ x ∉ dstNames i'.1)
    (h : KnownAt C k x c) : KnownAt (expI e C 0) (pcI e C k) x c := by
  obtain ⟨j, hj, hJ, hmid⟩ := h
  have hsj := pcI_succ e hJ
  rw [hmov] at hsj
  have hjk := pcI_mono e C (show j + 1 ≤ k by omega)
  refine ⟨pcI e C j, by simp only [List.length_singleton] at hsj; omega, ?_, ?_⟩
  · have := getElem?_expI_pcI e hJ (j := 0) (by rw [hmov]; simp)
    rw [Nat.add_zero, hmov] at this
    simpa using this
  · intro p h1 h2 i' hi'
    obtain ⟨j', i, r, hj', he, rfl⟩ := getElem?_expI_inv e C 0 p i' hi'
    rw [Nat.zero_add] at he
    have hr : r < (e j' i).length := (List.getElem?_eq_some_iff.mp he).1
    have hs' := pcI_succ e hj'
    change pcI e C j < pcI e C j' + r at h1
    change pcI e C j' + r < pcI e C k at h2
    have hjj : j < j' := by
      rcases Nat.lt_trichotomy j' j with hlt | rfl | hgt
      · have := pcI_mono e C (show j' + 1 ≤ j by omega)
        omega
      · rw [hJ] at hj'
        cases hj'
        rw [hmov] at hr
        simp only [List.length_singleton] at hr
        omega
      · exact hgt
    have hjk' : j' < k := by
      by_contra hc
      have := pcI_mono e C (show k ≤ j' by omega)
      omega
    obtain ⟨hl, hn | rfl⟩ := hmid j' hjj hjk' i hj'
    · obtain ⟨hl', hn'⟩ := hop j' i hj' hl hn i' (List.mem_of_getElem? he)
      exact ⟨hl', .inl hn'⟩
    · have hm := List.mem_of_getElem? he
      rw [hself, List.mem_singleton] at hm
      subst hm
      exact ⟨⟨_, _, _, rfl⟩, .inr rfl⟩

/-- **Known indices through an expansion** that keeps each access, each move of a constant
    and each self move, and that expands each operation not writing an access index into
    operations not writing it. -/
theorem idxKnown_expI {C : List LinstrRM}
    (hacc : ∀ j i i' x m, C[j]? = some i → i' ∈ e j i → AccIdx i' x m → e j i = [i])
    (hmov : ∀ j x c, e j (.Lopn [.reg x] "MOV:64" [.imm c], .reg none)
      = [(.Lopn [.reg x] "MOV:64" [.imm c], .reg none)])
    (hself : ∀ j x, e j (selfMovI x) = [selfMovI x])
    (hop : ∀ x, (∃ (k : Nat) (i : LinstrRM) (m : Nat), C[k]? = some i ∧ AccIdx i x m) →
      ∀ (j : Nat) (i : LinstrRM), C[j]? = some i →
      (∃ ds o ss, i.1 = .Lopn ds o ss) → x ∉ dstNames i.1 →
      ∀ i' ∈ e j i, (∃ ds o ss, i'.1 = .Lopn ds o ss) ∧ x ∉ dstNames i'.1)
    (h : IdxKnown C) : IdxKnown (expI e C 0) := by
  intro p ins x m hp hac
  obtain ⟨j, i, r, hj, he, rfl⟩ := getElem?_expI_inv e C 0 p ins hp
  rw [Nat.zero_add] at he
  have hE := hacc j i ins x m hj (List.mem_of_getElem? he) hac
  rw [hE] at he
  obtain ⟨rfl, rfl⟩ : r = 0 ∧ i = ins := by cases r <;> simp_all
  obtain ⟨c, hc, hK⟩ := h j i x m hj hac
  exact ⟨c, hc, knownAt_expI e (fun j' => hmov j' x c) (fun j' => hself j' x)
    (hop x ⟨j, i, m, hj, hac⟩) hK⟩

end Exp

section Fuse

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (expI fuseE fuseSiteExp fuseLo
  fuseMulHiRM fuseMulHiRM_eq wireOK)

/-- The fusion keeps a move of a constant. -/
theorem fuseE_movImm (L : List (Option String)) (j : Nat) (x : String) (c : Nat) :
    fuseE L j (.Lopn [.reg x] "MOV:64" [.imm c], .reg none)
      = [(.Lopn [.reg x] "MOV:64" [.imm c], .reg none)] := by
  unfold fuseE fuseSiteExp
  split <;> rfl

/-- The fusion keeps a self move. -/
theorem fuseE_selfMovI (L : List (Option String)) (j : Nat) (x : String) :
    fuseE L j (selfMovI x) = [selfMovI x] := by
  unfold fuseE fuseSiteExp
  split <;> rfl

/-- The fusion keeps an access. -/
theorem fuseE_acc (L : List (Option String)) (j : Nat) {i : LinstrRM} {x : String} {m : Nat}
    (h : AccIdx i x m) : fuseE L j i = [i] := by
  obtain ⟨ds, o, b, s, ss, w, h1, -⟩ := h
  obtain ⟨wi, t⟩ := i
  simp only at h1
  subst h1
  unfold fuseE fuseSiteExp
  split <;> (try split) <;> simp_all

/-- An expansion by the fusion that holds an access is the access alone. -/
theorem fuseE_of_mem_acc (L : List (Option String)) (j : Nat) {i i' : LinstrRM} {x : String}
    {m : Nat} (h : i' ∈ fuseE L j i) (ha : AccIdx i' x m) : fuseE L j i = [i] := by
  unfold fuseE at h ⊢
  split at h
  · unfold fuseSiteExp at h ⊢
    split at h
    · obtain ⟨ds, o, b, s, ss, w, h1, -⟩ := ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp at h1
    · rfl
  · rfl

/-- The instructions of the fusion of an operation are operations, and they write the names
    of the operation, `R15`, `RDX` and the low destination of its site. -/
theorem fuseE_dst (L : List (Option String)) (j : Nat) {i : LinstrRM}
    (hl : ∃ ds o ss, i.1 = .Lopn ds o ss) :
    ∀ i' ∈ fuseE L j i, (∃ ds o ss, i'.1 = .Lopn ds o ss) ∧ ∀ n ∈ dstNames i'.1,
      n ∈ dstNames i.1 ∨ n = "R15" ∨ n = "RDX" ∨ ∃ d, L[j]? = some (some d) ∧ n = d := by
  intro i' hi'
  unfold fuseE at hi'
  split at hi'
  · rename_i d hd
    unfold fuseSiteExp at hi'
    split at hi'
    · rename_i hd' h1 s2 he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
      rcases hi' with rfl | rfl | rfl | rfl <;>
        simp_all [dstNames, JasminLsemExportRewrites.opNames]
    · simp only [List.mem_singleton] at hi'
      subst hi'
      exact ⟨hl, fun n hn => .inl hn⟩
  · simp only [List.mem_singleton] at hi'
    subst hi'
    exact ⟨hl, fun n hn => .inl hn⟩

/-- **Known indices through the multiplication fusion**, at a body whose names the fusion
    leaves alone and whose access indices are not `R15`, not `RDX` and no low destination of
    a site. -/
theorem idxKnown_fuseMulHiRM {C : List LinstrRM} (hw : ∀ i ∈ C, wireOK i.1 = true)
    (hx : ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat), C[k]? = some i → AccIdx i x m →
      x ≠ "R15" ∧ x ≠ "RDX" ∧ ∀ (j : Nat) (d : String), (fuseLo C)[j]? = some (some d) → d ≠ x)
    (h : IdxKnown C) : IdxKnown (fuseMulHiRM C) := by
  rw [fuseMulHiRM_eq C hw]
  refine idxKnown_expI _ (fun j i i' x m _ _ ha => ?_) (fun j x c => fuseE_movImm _ j x c)
    (fun j x => fuseE_selfMovI _ j x) ?_ h
  · exact fuseE_of_mem_acc _ j (by assumption) ha
  · rintro x ⟨k, i0, m, hk, ha⟩ j i _ hl hn i' hi'
    obtain ⟨h1, h2⟩ := fuseE_dst (fuseLo C) j hl i' hi'
    obtain ⟨hR, hD, hL⟩ := hx k i0 x m hk ha
    refine ⟨h1, fun hm => ?_⟩
    rcases h2 x hm with h | h | h | ⟨d, hd, rfl⟩
    · exact hn h
    · exact hR h
    · exact hD h
    · exact hL j _ hd rfl

end Fuse

/-! ## 5. The webs and the parts -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webLook webLook_cases stepRen
  webRen)

/-- A web name of another name is no name without `#`. -/
theorem eq_of_webLook_eq {tab : X86Backend.ArrWebs.WebSt × Std.HashSet Nat × Std.HashSet Nat}
    {k : Nat} {y x : String} (hx : '#' ∉ x.toList) (h : webLook tab k y = x) : y = x := by
  rcases webLook_cases tab k y with h' | ⟨root, h'⟩
  · rw [← h, h']
  · refine absurd ?_ hx
    rw [← h, h', String.toList_append, String.toList_append]
    simp

/-- **Known indices through the webs**, at access indices without `#`. -/
theorem idxKnown_regionWebs (ex : List String) {r0 : Exported} (hK : IdxKnown r0.code)
    (hx : ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat), r0.code[k]? = some i →
      AccIdx i x m → '#' ∉ x.toList) :
    IdxKnown (regionWebs ex r0).code := by
  unfold regionWebs
  split
  · refine idxKnown_renArr _ (fun j => List.getElem?_mapIdx) ?_ hK
    intro k i x m hk ha j i' y hy
    have hx' := hx k i x m hk ha
    unfold stepRen at hy
    split at hy <;> exact eq_of_webLook_eq hx' hy
  · exact hK

/-- **Known indices of the code with the result copies.** -/
theorem idxKnown_regionCoCode (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    {code : List LinstrRM} (res : List LOperand) (cp : Option (String × String × Nat))
    (hK : IdxKnown code) : IdxKnown (regionCoCode σ nm t code res cp) := by
  unfold regionCoCode
  split
  · exact idxKnown_append hK (idxKnown_movesOf _)
  · exact idxKnown_append (idxKnown_append hK (idxKnown_movesOf _)) (idxKnown_resCopyCode _ _ _)

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseLo wireOK fuseMulHiRM)

/-- **Known indices of the code behind the prefix of the parts**, from known indices of the
    exported code: the coalescing renaming and the renamings by the pairs and the merge send
    no other name to an access index, and with sites of the multiplication fusion the code has
    no pair of an array self-move, the fusion leaves the names alone and no access index is
    `R15`, `RDX` or a low destination of a site. -/
theorem idxKnown_regionCoParts {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {t : JasminTy} {code : List LinstrRM} {res : List LOperand} {cert : List (String × String)}
    (d : CoParts) (hd : d = regionCoParts σ nm body t code res cert) (hK : IdxKnown code)
    (hA : ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat),
      (regionCoCode σ nm t code res (regionCopy σ nm t none code res))[k]? = some i →
      AccIdx i x m → ∀ y, canonMemrefName (regionAliasTab σ nm t none res
        (regionCoCode σ nm t code res (regionCopy σ nm t none code res))) y = x → y = x)
    (hps : ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat),
      (regionCoBody σ nm t code res)[k]? = some i → AccIdx i x m →
      ∀ y, renOf d.ps y = renOf d.ps x → y = x)
    (hτ : ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat), d.ren[k]? = some i →
      AccIdx i x m → ∀ y, renOf d.tau y = renOf d.tau x → y = x)
    (hNP : d.sites = true → ∀ k, selfPairB d.pre.length
      (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length) (d.pre ++ d.merged) k = false)
    (hF : d.sites = true → (∀ i ∈ d.merged, wireOK i.1 = true) ∧
      ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat), d.merged[k]? = some i →
        AccIdx i x m → x ≠ "R15" ∧ x ≠ "RDX" ∧
          ∀ (j : Nat) (dd : String), (fuseLo d.merged)[j]? = some (some dd) → dd ≠ x) :
    IdxKnown (d.fused.drop d.pre.length) := by
  have h1 := idxKnown_regionCoCode σ nm t res (regionCopy σ nm t none code res) hK
  have h2 : IdxKnown (regionCoBody σ nm t code res) :=
    idxKnown_renArr _ (fun j => List.getElem?_map) (fun k i x m hk ha _ _ y hy =>
      hA k i x m hk ha y hy) h1
  have h3 : IdxKnown d.ren := by
    subst hd
    exact idxKnown_map_renRM _ hps h2
  have h4 : IdxKnown d.merged := by
    have := idxKnown_map_renRM _ hτ h3
    subst hd
    exact this
  have hn : d.nop = selfNop d.pre.length (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length)
      (d.pre ++ d.merged) := by
    subst hd
    rfl
  have hfu : d.fused = if d.sites then d.pre ++ fuseMulHiRM (d.nop.drop d.pre.length)
      else d.nop := by
    subst hd
    rfl
  rw [hfu]
  split
  · rename_i hs
    rw [List.drop_left, hn, selfNop_eq_of_noPair (hNP hs), List.drop_left]
    obtain ⟨hw, hx⟩ := hF hs
    exact idxKnown_fuseMulHiRM hw hx h4
  · rw [hn]
    exact idxKnown_selfNop_drop _ h4

/-! ## 5. The fold positions -/

/-- **The fold class of an instruction** at the slot arrays `R`: a load of a slot array of the
    length of its tag into a name that is no cell and no slot array, an in-place store to a
    slot array of the length of its tag of a name that is no cell, an operation of `keepB`,
    an instruction of `keepRegB`, or a control instruction of `ctlB`. -/
def PosClass (R : Slots) (i : LinstrRM) : Prop :=
  (∃ d b x s n, i = (.Lopn [.reg d] "LOADIDX" [.arrIdx b x s], .load 64 n) ∧
      isArrB R b = true ∧ lenOf R b = some n ∧ isCellB R d = false ∧ isArrB R d = false)
  ∨ (∃ b x s v n, i = (.Lopn [.reg b] "STOREIDX" [.arrIdx b x s, .reg v], .store 64 n) ∧
      isArrB R b = true ∧ lenOf R b = some n ∧ isCellB R v = false)
  ∨ keepB R i = true
  ∨ keepRegB R i = true
  ∨ (isLopnB i = false ∧ ctlB i = true)

/-- **The fold positions from known indices and the fold class.** -/
theorem foldPos_of_posClass {R : Slots} {C : List LinstrRM} (hK : IdxKnown C)
    {k : Nat} {i : LinstrRM} (hk : C[k]? = some i) (h : PosClass R i) : FoldPos R C k i := by
  rcases h with ⟨d, b, x, s, n, rfl, hb, hn, hd1, hd2⟩ | ⟨b, x, s, v, n, rfl, hb, hn, hv⟩ |
      h | h | h
  · obtain ⟨c, hc, hkn⟩ := hK k _ x n hk ⟨_, _, _, _, _, 64, rfl, .inl rfl⟩
    exact .inl ⟨d, b, x, s, n, c, rfl, hb, hn, hd1, hd2, hc, hkn⟩
  · obtain ⟨c, hc, hkn⟩ := hK k _ x n hk ⟨_, _, _, _, _, 64, rfl, .inr rfl⟩
    exact .inr (.inl ⟨b, x, s, v, n, c, rfl, hb, hn, hv, hc, hkn⟩)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr h)))

/-- **The fold positions from known indices and the fold class** at every position. -/
theorem foldPos_of_idxKnown {R : Slots} {C : List LinstrRM} (hK : IdxKnown C)
    (hP : ∀ (k : Nat) (i : LinstrRM), C[k]? = some i → PosClass R i) :
    ∀ (k : Nat) (i : LinstrRM), C[k]? = some i → FoldPos R C k i :=
  fun k i hk => foldPos_of_posClass hK hk (hP k i hk)

/-! ## 6. The field domain -/

/-- **The access indices of the export of a program of the shape `LoadsChainK` are slot names**,
    which have no `#`. -/
theorem loadsChainK_export_hash {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (h : LoadsChainK (fun _ => none) p)
    (hn : nArgs ≤ Γ.length) {n : Nat} {r : Exported}
    (hr : exportR nArgs fn p Γ.length n = some r) :
    ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat), r.code[k]? = some i → AccIdx i x m →
      '#' ∉ x.toList := by
  intro k i x m hk ha
  obtain ⟨c, -, j, -, hJ, -⟩ := loadsChainK_export_knownAt h hn hr k i x m hk ha
  obtain ⟨o, ss, h0⟩ := loadsChainK_export_shape h hr j _ hJ
  simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq] at h0
  rw [h0.1.1]
  exact hash_not_mem_regName _

/-- **Every access index of the code `C` has the property `P`.** -/
def AccIn (P : String → Prop) (C : List LinstrRM) : Prop :=
  ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat), C[k]? = some i → AccIdx i x m → P x

/-- The access indices along a position-preserving map that keeps the index of an access. -/
theorem accIn_of_getElem? {P : String → Prop} {C C' : List LinstrRM}
    (g : Nat → LinstrRM → LinstrRM) (hC : ∀ j, C'[j]? = (C[j]?).map (g j))
    (hacc : ∀ (j : Nat) (i : LinstrRM) (x : String) (m : Nat), AccIdx (g j i) x m →
      AccIdx i x m)
    (h : AccIn P C) : AccIn P C' := by
  intro k i x m hk ha
  rw [hC] at hk
  obtain ⟨i0, hi0, rfl⟩ := Option.map_eq_some_iff.mp hk
  exact h k i0 x m hi0 (hacc k i0 x m ha)

/-- The access indices of an appended code. -/
theorem accIn_append {P : String → Prop} {C D : List LinstrRM} (hC : AccIn P C)
    (hD : AccIn P D) : AccIn P (C ++ D) := by
  intro k i x m hk ha
  by_cases hlt : k < C.length
  · rw [List.getElem?_append_left hlt] at hk
    exact hC k i x m hk ha
  · rw [List.getElem?_append_right (by omega)] at hk
    exact hD _ i x m hk ha

/-- A name whose first character is `r`. -/
def HeadR (x : String) : Prop := x.toList.head? = some 'r'

/-- The access indices of the code with the result copies begin with `r` when those of the
    code do. -/
theorem accIn_regionCoCode (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    {code : List LinstrRM} (res : List LOperand) (cp : Option (String × String × Nat))
    (hK : AccIn HeadR code) : AccIn HeadR (regionCoCode σ nm t code res cp) := by
  have hmv : ∀ ps, AccIn HeadR (JasminLsemRenameLoop.movesOf ps) := by
    intro ps k i x m hk ha
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hk)
    exact absurd ha not_accIdx_reg
  have hcp : ∀ src D m', AccIn HeadR (resCopyCode src D m') := by
    intro src D m' k i x m hk ha
    obtain ⟨c, -, j, -, hJ, -⟩ := idxKnown_resCopyCode src D m' k i x m hk ha
    have hlt : j < 3 * m' := by
      have := (List.getElem?_eq_some_iff.mp hJ).1
      rwa [length_resCopyCode] at this
    obtain ⟨j', -, ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩⟩ :=
      resCopyCode_at (src := src) (D := D) (m := m') hlt <;> rw [hJ] at h <;>
      simp only [movImmI, movI, Option.some.injEq, Prod.mk.injEq, LinstrR.Lopn.injEq,
        List.cons.injEq, LOperand.reg.injEq, reduceCtorEq, false_and, and_false] at h
    rw [h.1.1.1]
    unfold HeadR copyIdx
    decide
  unfold regionCoCode
  split
  · exact accIn_append hK (hmv _)
  · exact accIn_append (accIn_append hK (hmv _)) (hcp _ _ _)

/-- **The access indices of the export of a program of the shape `LoadsChainK` are slot
    names.** -/
theorem loadsChainK_export_slotIdx {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} (h : LoadsChainK (fun _ => none) p)
    (hn : nArgs ≤ Γ.length) {n : Nat} {r : Exported}
    (hr : exportR nArgs fn p Γ.length n = some r) : AccIn (fun x => ∃ s, x = regName s) r.code := by
  intro k i x m hk ha
  obtain ⟨c, -, j, -, hJ, -⟩ := loadsChainK_export_knownAt h hn hr k i x m hk ha
  obtain ⟨o, ss, h0⟩ := loadsChainK_export_shape h hr j _ hJ
  simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq] at h0
  exact ⟨_, h0.1.1⟩

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **The access indices of the coalesced code of the field domain begin with `r`.** -/
theorem fieldBody_accIn (hB : FieldBody e σ fname b t r cert)
    (hL : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → LoadsChainK (fun _ => none) (legalizeRegion q')) :
    AccIn HeadR (regionCoBody σ exportReg t r.code r.res) := by
  have hr : AccIn HeadR r.code := by
    obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, -, -, -⟩ := hB
    have hK := hL t0 q q' hq hq'
    have h0 := loadsChainK_export_slotIdx hK le_rfl hr0
    have h1 : AccIn HeadR r0.code := fun k i x m hk ha => by
      obtain ⟨s, rfl⟩ := h0 k i x m hk ha
      simp [HeadR, regName, String.toList_append]
    rw [regionWebsAt_none]
    unfold regionWebs
    split
    · exact accIn_of_getElem? _ (fun j => List.getElem?_mapIdx)
        (fun _ _ _ _ ha => accIdx_of_renArr _ ha) h1
    · exact h1
  exact accIn_of_getElem? _ (fun j => List.getElem?_map) (fun _ _ _ _ ha => accIdx_of_renArr _ ha)
    (accIn_regionCoCode σ exportReg t r.res _ hr)

/-- **The pairs of the field domain fix the access indices and send no other name to one.** -/
theorem fieldDom_renOf_ps (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert)
    {x : String} (hx : HeadR x) (y : String)
    (hy : renOf (regionCoParts σ exportReg b t r.code r.res cert).ps y
      = renOf (regionCoParts σ exportReg b t r.code r.res cert).ps x) : y = x := by
  obtain ⟨B, tbl, hc, rfl⟩ := cert_allocCertOf h hB
  change renOf (certArgs σ (allocCertOf B tbl)) y = renOf (certArgs σ (allocCertOf B tbl)) x at hy
  unfold certArgs at hy
  rw [RegionAllocMapComplete.renOf_filter_allocCertOf,
    RegionAllocMapComplete.renOf_filter_allocCertOf] at hy
  have hxa : isArgNameB σ x = false := by
    cases hb : isArgNameB σ x
    · rfl
    · simp only [isArgNameB, List.any_eq_true, beq_iff_eq] at hb
      obtain ⟨j, -, hj⟩ := hb
      unfold HeadR at hx
      rw [← hj] at hx
      simp [argName, String.toList_append] at hx
  have hxc : CodeName x := (codeName_iff x).mpr (.inl hx)
  simp only [hxa, Bool.false_eq_true, and_false, ite_false] at hy
  split_ifs at hy
  · have hp := physName_allocName (tbl := tbl) hc y
    rw [hy] at hp
    exact absurd hxc hp.not_codeName
  · exact hy

/-- The pairs of the field domain fix a name that begins with `r`. -/
theorem fieldDom_renOf_ps_fix (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert)
    {x : String} (hx : HeadR x) :
    renOf (regionCoParts σ exportReg b t r.code r.res cert).ps x = x := by
  obtain ⟨B, tbl, hc, rfl⟩ := cert_allocCertOf h hB
  change renOf (certArgs σ (allocCertOf B tbl)) x = x
  unfold certArgs
  rw [RegionAllocMapComplete.renOf_filter_allocCertOf]
  have hxa : isArgNameB σ x = false := by
    cases hb : isArgNameB σ x
    · rfl
    · simp only [isArgNameB, List.any_eq_true, beq_iff_eq] at hb
      obtain ⟨j, -, hj⟩ := hb
      unfold HeadR at hx
      rw [← hj] at hx
      simp [argName, String.toList_append] at hx
  simp [hxa]

/-- The access indices along a renaming of names that fixes them. -/
theorem accIn_map_renRM {P : String → Prop} {C : List LinstrRM} (f : String → String)
    (hf : ∀ x, P x → f x = x) (h : AccIn P C) : AccIn P (C.map (renRM f)) := by
  intro k i x m hk ha
  rw [List.getElem?_map] at hk
  obtain ⟨i0, hi0, rfl⟩ := Option.map_eq_some_iff.mp hk
  obtain ⟨x0, rfl, ha0⟩ := accIdx_of_renRM f ha
  have hp := h k i0 x0 m hi0 ha0
  rw [hf x0 hp]
  exact hp

/-- **Known indices of the webs of the export** on the field domain, when the legalized chain
    output has the shape `LoadsChainK`. -/
theorem fieldBody_idxKnown (hB : FieldBody e σ fname b t r cert)
    (hL : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → LoadsChainK (fun _ => none) (legalizeRegion q')) :
    IdxKnown r.code := by
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, -, -, -⟩ := hB
  have hK := hL t0 q q' hq hq'
  rw [regionWebsAt_none]
  exact idxKnown_regionWebs _ (loadsChainK_export_knownAt hK le_rfl hr0)
    (loadsChainK_export_hash hK le_rfl hr0)

/-- **The fold positions of the field domain (the field `foldPos` of `FieldDomOpen`)** from the
    shape `LoadsChainK` of the legalized chain output, the conditions of
    `idxKnown_regionCoParts` on the renamings, the self-moves and the fusion, and the fold
    class of each instruction of the code behind the prefix. -/
theorem fieldDom_foldPos_of_back (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert)
    (hL : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → LoadsChainK (fun _ => none) (legalizeRegion q'))
    (hA : ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat),
      (regionCoCode σ exportReg t r.code r.res (regionCopy σ exportReg t none r.code r.res))[k]?
        = some i → AccIdx i x m →
      ∀ y, canonMemrefName (regionAliasTab σ exportReg t none r.res
        (regionCoCode σ exportReg t r.code r.res
          (regionCopy σ exportReg t none r.code r.res))) y = x → y = x)
    (hNP : (regionCoParts σ exportReg b t r.code r.res cert).sites = true →
      ∀ k, selfPairB (regionCoParts σ exportReg b t r.code r.res cert).pre.length
        (liveAt (tabAt (regionCoParts σ exportReg b t r.code r.res cert).liveM)
          ((regionCoParts σ exportReg b t r.code r.res cert).pre
            ++ (regionCoParts σ exportReg b t r.code r.res cert).merged).length)
        ((regionCoParts σ exportReg b t r.code r.res cert).pre
          ++ (regionCoParts σ exportReg b t r.code r.res cert).merged) k = false)
    (hw : (regionCoParts σ exportReg b t r.code r.res cert).sites = true →
      ∀ i ∈ (regionCoParts σ exportReg b t r.code r.res cert).merged, wireOK i.1 = true)
    (hlo : (regionCoParts σ exportReg b t r.code r.res cert).sites = true →
      ∀ (k : Nat) (i : LinstrRM) (x : String) (m : Nat),
        (regionCoParts σ exportReg b t r.code r.res cert).merged[k]? = some i →
        AccIdx i x m → ∀ (j : Nat) (dd : String),
        (fuseLo (regionCoParts σ exportReg b t r.code r.res cert).merged)[j]? = some (some dd) →
        dd ≠ x)
    (hP : ∀ (k : Nat) (i : LinstrRM),
      ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      PosClass (regionCoParts σ exportReg b t r.code r.res cert).cells i) :
    ∀ k i, ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      FoldPos (regionCoParts σ exportReg b t r.code r.res cert).cells
        ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
          (regionCoParts σ exportReg b t r.code r.res cert).pre.length) k i := by
  have hτ := fieldDom_tau_nil h hB
  have hid : ∀ x, renOf (regionCoParts σ exportReg b t r.code r.res cert).tau x = x := by
    intro x
    rw [hτ]
    rfl
  have hR := fieldBody_accIn hB hL
  have hRen : AccIn HeadR (regionCoParts σ exportReg b t r.code r.res cert).ren :=
    accIn_map_renRM _ (fun x hx => fieldDom_renOf_ps_fix h hB hx) hR
  have hM : AccIn HeadR (regionCoParts σ exportReg b t r.code r.res cert).merged :=
    accIn_map_renRM _ (fun x _ => hid x) hRen
  refine foldPos_of_idxKnown (idxKnown_regionCoParts _ rfl (fieldBody_idxKnown hB hL) hA
    (fun k i x m hk ha y hy => fieldDom_renOf_ps h hB (hR k i x m hk ha) y hy)
    (fun _ _ _ _ _ _ y hy => by rwa [hid, hid] at hy) hNP
    (fun hs => ⟨hw hs, fun k i x m hk ha => ?_⟩)) hP
  have hx := hM k i x m hk ha
  refine ⟨fun he => ?_, fun he => ?_, hlo hs k i x m hk ha⟩ <;>
    (subst he; revert hx; unfold HeadR; decide)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
