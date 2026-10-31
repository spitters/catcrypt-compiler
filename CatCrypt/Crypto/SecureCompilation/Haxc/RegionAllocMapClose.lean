/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapComplete
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInit

@[expose] public section

set_option autoImplicit false

/-!
# The register-merge check of a region export, assembled

The check `regionMergeB` of the region gate accepts the merge pairs of the parts
`regionCoParts` when the merge passes `regCoB` at the register liveness table `liveRegTab`
of the reference. `RegionAllocMapComplete.regionMergeB_regionCoParts_of_cover` reduces it to
the conditions `InstrCover` at every position of the renamed code. This module discharges the
structural conditions on the export without a callee: the table is closed
(`liveRegTab_stable`), the instructions of the renamed code have the shape `CoShape` (no
unconditional jump, a conditional jump on the zero flag, one register destination per
operation), they pass the call check, and their arrays are among the array names of the
parts. What remains is a condition on the merge: it fixes the empty name, the names live at
the entry of the renamed code and the targets of the result copy, gives no written name the
empty image, and separates a name live after a write from the written name.

## Main results

* `exportR_coShape`: every instruction of the export of a program on x86 has the shape
  `CoShape`.
* `coShape_regionCoParts_ren`: so has every instruction of the renamed code of the parts
  without a callee, when the exported code has it.
* `instrCover_regionCoParts`: the conditions `InstrCover` at every position of the renamed
  code from the shape and from the separation of the merge.
* `regionMergeB_regionLprogC`: for an export `exportR .. = some r` and an allocation
  `regionLprogC a p none ex = some (P, cert)`, the parts at `cert` pass `regionMergeB` under
  the conditions on the merge listed above.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapClose

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findLabelMem IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames defNames regDefs
  arrDefs arrUse? jumpLabel?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data x86Data_loopGuard
  x86Data_zeroTripGuard)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaData callShadow)
open RegionAllocMapComplete RegionExportDefInit

/-! ## 1. The shape of the export -/

section Pieces

theorem coShape_movI (dst : String) (src : LOperand) : CoShape (movI dst src) :=
  coShape_lopn rfl

theorem coShape_label (l : LLabel) : CoShape (labelI l) :=
  coShape_other (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)

theorem coShape_movs {α : Type} (l : List α) (f : α → String) (g : α → LOperand) :
    ∀ i ∈ l.map (fun a => movI (f a) (g a)), CoShape i := by
  intro i hi
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hi
  exact coShape_movI _ _

theorem coShape_arrMoves (z t : String) (mv : List ArrMove) :
    ∀ i ∈ arrMoves z t mv, CoShape i := by
  intro i hi
  obtain ⟨a, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact coShape_lopn rfl

theorem coShape_typedMoves (z t : String) (tp : List (JasminTy × String × String)) :
    ∀ i ∈ typedMoves z t tp, CoShape i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact coShape_arrMoves _ _ _ i hi
  · exact coShape_movs _ (fun p : String × String => p.1) (fun p => .reg p.2) i hi

theorem coShape_seedMoves (car : List String) (ops : List LOperand) :
    ∀ i ∈ seedMoves car ops, CoShape i :=
  coShape_movs _ (fun p : String × LOperand => p.1) (fun p => p.2)

theorem coShape_arrParMoves (z t : String) (D : Nat) (mv : List ArrMove) :
    ∀ i ∈ arrParMoves z t D mv, CoShape i := by
  intro i hi
  unfold arrParMoves at hi
  split at hi
  · exact coShape_arrMoves _ _ _ i hi
  · rcases List.mem_append.mp hi with hi | hi <;> exact coShape_arrMoves _ _ _ i hi

theorem coShape_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) :
    ∀ i ∈ ExportRegions.parMoves D tgts ops, CoShape i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact coShape_movs _ (fun p : LOperand × Nat => regName (D + p.2)) (fun p => p.1) i hi
  · exact coShape_movs _ (fun p : String × Nat => p.1) (fun p => .reg (regName (D + p.2))) i hi

theorem coShape_advanceOps (idx ctr : String) : ∀ i ∈ advanceOps idx ctr, CoShape i := by
  intro i hi
  simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact coShape_lopn rfl

theorem coShape_ifResMoves (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    ∀ i ∈ ifResMoves rs d D ops, CoShape i := by
  intro i hi
  unfold ifResMoves at hi
  rcases List.mem_append.mp hi with hi | hi
  · split at hi
    · simp at hi
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact coShape_movI _ _
      · exact coShape_arrParMoves _ _ _ _ i hi
  · exact coShape_parMoves _ _ _ i hi

theorem coShape_flagWord (I : IsaData) (r z : String) (op : LOperand) :
    ∀ i ∈ flagWord I r z op, CoShape i := by
  intro i hi
  unfold flagWord at hi
  split at hi
  · split at hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> exact coShape_lopn rfl
    · simp at hi
  · simp only [List.mem_singleton] at hi
    subst hi
    exact coShape_movI _ _

theorem coShape_zeroTrip (c : String) (t e : LLabel) :
    ∀ i ∈ (x86Data.zeroTripGuard c t e).map guardI, CoShape i := by
  rw [x86_zeroTrip]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact coShape_lopn rfl
  · exact coShape_cond rfl (Or.inl rfl)

theorem coShape_loopGuard (c : String) (t : LLabel) :
    ∀ i ∈ (x86Data.loopGuard c t).map guardI, CoShape i := by
  rw [x86_loopGuard]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact coShape_lopn rfl
  · exact coShape_cond rfl (Or.inr rfl)

end Pieces

/-- **Every instruction of the export has the shape `CoShape`** (`exportR_coShape`): the export
    of a program on x86 has no unconditional jump, its conditional jumps read the zero flag
    (`Z` at a zero-trip guard, `NZ` at a loop guard), and each of its operations has one
    register destination. -/
theorem exportR_coShape (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r → ∀ i ∈ r.code, CoShape i := by
  have hlab : ∀ l, CoShape (labelI l) := coShape_label
  induction p with
  | ret vs =>
      intro d n r h
      simp only [exportR, Option.some.injEq] at h
      subst h
      intro i hi; simp at hi
  | var e k ih =>
      intro d n r h
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨o, ss, tag, hb, -⟩ := bindOps_shape nArgs e d
        rw [hb, List.mem_singleton] at hi
        subst hi
        exact coShape_lopn rfl
      · exact ih _ _ _ hk i hi
  | call f args k ih =>
      intro d n r h
      obtain ⟨-, rk, hk, rfl⟩ := exportR_call_eq_some.mp h
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact coShape_lopn rfl
      · exact ih _ _ _ hk i hi
  | forLoop count inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hB := ihb _ _ _ hb
      have hK := ihk _ _ _ hk
      show ∀ i ∈ _, CoShape i
      simp only [Exported.prepend, forArrFrame,
        List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true, List.map_cons, List.map_nil]
      repeat' first
        | exact hB
        | exact hK
        | exact hT'
        | exact hE
        | exact hlab _
        | exact coShape_movI _ _
        | exact coShape_typedMoves _ _ _
        | exact coShape_seedMoves _ _
        | exact coShape_arrParMoves _ _ _ _
        | exact coShape_parMoves _ _ _
        | exact coShape_advanceOps _ _
        | exact coShape_ifResMoves _ _ _ _
        | exact coShape_flagWord _ _ _ _
        | exact coShape_lopn rfl
        | exact coShape_zeroTrip _ _ _
        | exact coShape_loopGuard _ _
        | exact coShape_label _
        | exact coShape_cond rfl (Or.inl rfl)
        | exact coShape_cond rfl (Or.inr rfl)
        | constructor
  | ifThenElse cond thn els k iht ihe ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      have hT' := iht _ _ _ ht
      have hE := ihe _ _ _ he
      have hK := ihk _ _ _ hk
      show ∀ i ∈ _, CoShape i
      simp only [Exported.prepend, ifFrame,
        List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true, List.map_cons, List.map_nil]
      repeat' first
        | exact hB
        | exact hK
        | exact hT'
        | exact hE
        | exact hlab _
        | exact coShape_movI _ _
        | exact coShape_typedMoves _ _ _
        | exact coShape_seedMoves _ _
        | exact coShape_arrParMoves _ _ _ _
        | exact coShape_parMoves _ _ _
        | exact coShape_advanceOps _ _
        | exact coShape_ifResMoves _ _ _ _
        | exact coShape_flagWord _ _ _ _
        | exact coShape_lopn rfl
        | exact coShape_zeroTrip _ _ _
        | exact coShape_loopGuard _ _
        | exact coShape_label _
        | exact coShape_cond rfl (Or.inl rfl)
        | exact coShape_cond rfl (Or.inr rfl)
        | constructor
  | whileLoop inits body k ihb ihk =>
      intro d n r h
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hB := ihb _ _ _ hb
      have hK := ihk _ _ _ hk
      show ∀ i ∈ _, CoShape i
      simp only [Exported.prepend, whileFrame,
        List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true, List.map_cons, List.map_nil]
      repeat' first
        | exact hB
        | exact hK
        | exact hT'
        | exact hE
        | exact hlab _
        | exact coShape_movI _ _
        | exact coShape_typedMoves _ _ _
        | exact coShape_seedMoves _ _
        | exact coShape_arrParMoves _ _ _ _
        | exact coShape_parMoves _ _ _
        | exact coShape_advanceOps _ _
        | exact coShape_ifResMoves _ _ _ _
        | exact coShape_flagWord _ _ _ _
        | exact coShape_lopn rfl
        | exact coShape_zeroTrip _ _ _
        | exact coShape_loopGuard _ _
        | exact coShape_label _
        | exact coShape_cond rfl (Or.inl rfl)
        | exact coShape_cond rfl (Or.inr rfl)
        | constructor


/-! ## 2. The shape of the renamed code -/

theorem coShape_resCopyCode (src D : String) (m : Nat) :
    ∀ i ∈ resCopyCode src D m, CoShape i := by
  intro i hi
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl <;> exact coShape_lopn rfl

theorem coShape_regionCoCode (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    {code : List LinstrRM} (res : List LOperand) (cp : Option (String × String × Nat))
    (hc : ∀ i ∈ code, CoShape i) : ∀ i ∈ regionCoCode σ nm t code res cp, CoShape i := by
  intro i hi
  unfold regionCoCode at hi
  split at hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact hc i hi
    · exact coShape_movesOf _ i hi
  · rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact hc i hi
      · exact coShape_movesOf _ i hi
    · exact coShape_resCopyCode _ _ _ i hi

/-- **The renamed code of the parts has the shape `CoShape`** when the exported code has it:
    the result copies are moves and the array result copy is loads and stores, and the
    renaming of the array positions and of the register names keeps the shape. -/
theorem coShape_regionCoParts_ren (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) {code : List LinstrRM} (res : List LOperand) (cert : List (String × String))
    (callee : Option CalleeData) (hc : ∀ i ∈ code, CoShape i) :
    ∀ i ∈ (regionCoParts σ nm body t code res cert callee).ren, CoShape i := by
  intro i hi
  have hi' : i ∈ (regionCoBody σ nm t code res callee).map
      (JasminLsemExportTransfer.renRM (renOf (certArgs σ cert))) := hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
  unfold regionCoBody at hj
  obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hj
  exact coShape_renRM _ (coShape_renArr _ (coShape_regionCoCode σ nm t res _ hc j' hj'))

/-! ## 3. The cover at every position -/

/-- **The conditions on the merge** of the parts `d` that the structure of the export does
    not give: the merge `renOf d.tau` fixes the empty name, the names of the table at the
    first position of the renamed code and the targets of the result copy; no name written
    in the renamed code has the empty image; and a name live after a write in the renamed
    code and the written name have distinct images unless they are equal. -/
structure MergeSep (d : CoParts) : Prop where
  /-- The empty name is fixed. -/
  empty : renOf d.tau "" = ""
  /-- The names live at the first position of the renamed code are fixed. -/
  entry : ∀ r ∈ tabAt d.live d.pre.length, renOf d.tau r = r
  /-- The targets of the result copy are fixed. -/
  outs : ∀ y ∈ d.outs, renOf d.tau y = y
  /-- No written name has the empty image. -/
  defNe : ∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
    ∀ x ∈ regDefs i, renOf d.tau x ≠ ""
  /-- A name live after a write and the written name have distinct images. -/
  sep : ∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
    ∀ y ∈ tabAt d.live (k + 1), ∀ x ∈ regDefs i, y ≠ x → renOf d.tau y ≠ renOf d.tau x

theorem mem_ren_of_getElem? {pre ren : List LinstrRM} {k : Nat} {i : LinstrRM}
    (hk : pre.length ≤ k) (hi : (pre ++ ren)[k]? = some i) : i ∈ ren := by
  rw [List.getElem?_append_right hk] at hi
  exact List.mem_of_getElem? hi

theorem mem_arrNames_use {C : List LinstrRM} {i : LinstrRM} (hi : i ∈ C) {a : String}
    (ha : a ∈ (arrUse? i).toList) : a ∈ arrNames C := by
  unfold arrNames
  rw [List.mem_eraseDups]
  exact List.mem_flatMap.mpr ⟨i, hi, List.mem_append_left _ ha⟩

theorem mem_arrNames_def {C : List LinstrRM} {i : LinstrRM} (hi : i ∈ C) {a : String}
    (ha : a ∈ arrDefs i) : a ∈ arrNames C := by
  unfold arrNames
  rw [List.mem_eraseDups]
  exact List.mem_flatMap.mpr ⟨i, hi, List.mem_append_right _ ha⟩

/-- **The conditions `InstrCover` at every position of the renamed code** of the parts
    without a callee, from the shape `CoShape` of the exported code and the conditions
    `MergeSep` on the merge: the table is closed (`liveRegTab_stable`), the shape gives the
    condition check, the absence of unconditional jumps and the single register
    destination, the arrays of an instruction are among the array names of the parts, and
    without a callee every instruction passes the call check. -/
theorem instrCover_regionCoParts (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) {code : List LinstrRM} (res : List LOperand) (cert : List (String × String))
    (hc : ∀ i ∈ code, CoShape i) (hM : MergeSep (regionCoParts σ nm body t code res cert none))
    {k : Nat} {i : LinstrRM}
    (hk : (regionCoParts σ nm body t code res cert none).pre.length ≤ k)
    (hi : ((regionCoParts σ nm body t code res cert none).pre
      ++ (regionCoParts σ nm body t code res cert none).ren)[k]? = some i) :
    InstrCover (renOf (regionCoParts σ nm body t code res cert none).tau)
      ((regionCoParts σ nm body t code res cert none).pre
        ++ (regionCoParts σ nm body t code res cert none).ren)
      (regionCoParts σ nm body t code res cert none).live
      (regionCoParts σ nm body t code res cert none).arrs
      (regionCoParts σ nm body t code res cert none).aa
      (regionCoParts σ nm body t code res cert none).ao k i := by
  have hmem := mem_ren_of_getElem? hk hi
  have hs := coShape_regionCoParts_ren σ nm body t res cert none hc i hmem
  exact
    { need := liveRegTab_closed (liveRegTab_stable _ _) hi
      cond := condOKB_of_coShape hs
      noGoto := hs.1
      arrUse := fun a ha => List.mem_append_left _ (List.mem_append_left _
        (mem_arrNames_use hmem ha))
      arrDef := fun a ha => List.mem_append_left _ (List.mem_append_left _
        (mem_arrNames_def hmem ha))
      defs := regDefs_length_le_of_coShape hs
      defNe := hM.defNe k i hk hi
      inj := hM.sep k i hk hi
      call := regCallB_none _ _ _ k i }

theorem certMergeKeep_of_mem_arrs {σ : AbiLayout} {arrs X : List String} {x : String}
    (h : x ∈ arrs) : certMergeKeep σ arrs X x = false := by
  simp [certMergeKeep, h]

/-- **The array names of the parts are fixed by the merge**: `certMerge` keeps no pair whose
    first component is an array name of the parts. -/
theorem renOf_tau_arrs (σ : AbiLayout) (nm : String → String) (body : Lcmd) (t : JasminTy)
    (code : List LinstrRM) (res : List LOperand) (cert : List (String × String))
    (callee : Option CalleeData) :
    ∀ a ∈ (regionCoParts σ nm body t code res cert callee).arrs,
      renOf (regionCoParts σ nm body t code res cert callee).tau a = a := by
  intro a ha
  exact renOf_certMerge_of_not (certMergeKeep_of_mem_arrs ha)

/-! ## 4. The check of the register merge -/

/-- **The check of the register merge of a region export without a callee**
    (`regionMergeB_export`): for an export `r` of a program on x86 from the depth and the
    argument count `Γ.length` and the label `0`, and every certificate `cert`, the parts
    `regionCoParts σ nm body t r.code r.res cert` pass `regionMergeB` when the merge satisfies
    `MergeSep`. -/
theorem regionMergeB_export (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 x86Data = some r) (cert : List (String × String))
    (hM : MergeSep (regionCoParts σ nm body t r.code r.res cert none)) :
    regionMergeB (regionCoParts σ nm body t r.code r.res cert none) = true :=
  regionMergeB_regionCoParts_of_cover σ nm body t r.code r.res cert none hM.empty
    (renOf_tau_arrs σ nm body t r.code r.res cert none) hM.entry
    (fun _ _ hk hi => instrCover_regionCoParts σ nm body t r.res cert
      (exportR_coShape Γ.length fn p Γ.length 0 r hr) hM hk hi) hM.outs

/-- **The check of the register merge at the allocation of a region export**
    (`regionMergeB_regionLprogC`): when the allocation `regionLprogC a p none ex` of a
    program on x86 without a callee returns the program `P` and the certificate `cert`, the
    program has an export `r` from the depth and the argument count `Γ.length` and the label
    `0`, and the parts `regionCoParts σ nm body t r.code r.res cert` of the gate pass
    `regionMergeB` when the merge satisfies `MergeSep`. -/
theorem regionMergeB_regionLprogC (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (ex : List String) {P : Lprog}
    {cert : List (String × String)} (hP : regionLprogC a p none ex = some (P, cert)) :
    ∃ r, exportR Γ.length a.fname p Γ.length 0 x86Data = some r
      ∧ (MergeSep (regionCoParts σ nm body t r.code r.res cert none) →
        regionMergeB (regionCoParts σ nm body t r.code r.res cert none) = true) := by
  unfold regionLprogC regionAllocC at hP
  cases hr : exportR Γ.length a.fname p Γ.length 0 x86Data with
  | none =>
    rw [hr] at hP
    cases hP
  | some r => exact ⟨r, rfl, regionMergeB_export σ nm body t a.fname p hr cert⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapClose
