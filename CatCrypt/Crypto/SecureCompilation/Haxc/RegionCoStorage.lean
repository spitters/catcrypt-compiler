/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportForms

@[expose] public section

set_option autoImplicit false

/-!
# Disjoint storage classes of the region export: the entry conjunct

The coalescing completeness theorems of `RegionCoComplete` take the hypothesis
`StorageDisjoint` on the code with the result copies `regionCoCode` of an export. Its second
conjunct states that no array name live at the entry (`PLive … 0`) is assigned by an
instruction of the code (`lopnDst`). This module proves that conjunct on every export of the
call-free arm on x86.

## The argument

A name live at the entry is read as an array on a walk from the entry along which no
instruction writes it as an array. The tagged code of `RegionExportDefInitSort` renames every
array position `x` to `tagA x`, and the certificate of definite assignment of the tagged code
`cert_regionCoCodeS` holds the tagged name of an array before it is read. The certificate is
closed backwards along `webSuccs`, which contains every successor `Succ` of the coalescing
check (`mem_webSuccs_of_succ`), and a tagged name that a tagged instruction writes is the
array that instruction writes (`WriteSorted`). Hence a name live at a position has its tagged
name in the certificate there or among the names read without a prior write
(`pLive_tagA`). The certificate is empty at the entry, so a name live at the entry has its
tagged name among the argument names in both namespaces (`ArgS`), and it is an argument name
`argName j`.

No instruction of the code assigns an argument name: the export writes names beginning with
`r` or `L` (`RegionAllocMapLive.exportR_defNames`), the result move writes the export name
of the result register, a general-purpose name of the printed body, and the result copy
writes its index and scratch registers and the versions `copyName D (j + 1)` of the result
buffer, none of which is of the form `"a" ++ toString j`.

## Main results

* `mem_webSuccs_of_succ`: the successors of the coalescing check are successors of
  `webSuccs`.
* `pLive_tagA`: a name live at a position has its tagged name in a certificate of the tagged
  code or among its names read without a prior write.
* `pLive_entry_argName`: a name live at the entry of the code with the result copies of an
  export is an argument name.
* `regionCoCode_lopnDst_ne_argName`: that code assigns no argument name.
* `storageDisjoint_entry`: the second conjunct of `StorageDisjoint` on that code.
* `storageDisjoint_iff_classes`: on that code `StorageDisjoint` is its first conjunct.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoStorage

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames defNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (movesOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webSuccs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (arrWrite)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk gpList)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoComplete (lopnDst StorageDisjoint NoShadow InUse
  noRealAlias_of_storageDisjoint regionCoStage_coalesce_of exportR_tagOK exportR_noShadow
  x86Data_guardsNoShadow)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInit (Cert webSuccs_congr
  findLabelMem_map wrArr_eq_arrWrite defNames_Lopn symReads blk_movs)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInitSort
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapLive (ExportRegName exportR_defNames)

/-! ## 1. The successors of the coalescing check -/

/-- The arm of a conditional jump of the check is that of an `Lcond`. -/
theorem lcond_of_armOf_cc {i : LinstrRM} {lbl : LLabel} (h : armOf i = .cc lbl) :
    ∃ c, i.1 = .Lcond c lbl := by
  obtain ⟨w, tag⟩ := i
  unfold armOf at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (rename_i hf
       unfold JasminLsemMemFlagGuard.flagCondCC? at hf
       split at hf <;> simp_all)
    | simp_all

/-- The arm of an unconditional jump of the check is that of an `Lgoto`. -/
theorem lgoto_of_armOf_goto {i : LinstrRM} {lbl : LLabel} (h : armOf i = .goto lbl) :
    ∃ x, i.1 = .Lgoto (x, lbl) := by
  obtain ⟨w, tag⟩ := i
  unfold armOf at h
  repeat' split at h
  all_goals simp_all

/-- **A successor of the coalescing check is a successor of `webSuccs`.** -/
theorem mem_webSuccs_of_succ {body : List LinstrRM} {k k' : Nat} {i : LinstrRM}
    (h : Succ body k i k') : k' ∈ webSuccs body k i := by
  unfold Succ at h
  have hnext : (∀ x l, i.1 ≠ .Lgoto (x, l)) → k + 1 ∈ webSuccs body k i := by
    intro hg
    obtain ⟨w, tag⟩ := i
    cases w with
    | Lgoto tg => exact absurd rfl (hg tg.1 tg.2)
    | _ => simp [webSuccs]
  rcases ha : armOf i with ⟨dst, f, srcs⟩ | _ | _ | lbl | lbl | _ | _ <;>
    rw [ha] at h <;> simp only [SuccA] at h
  · subst h
    refine hnext fun x l hx => ?_
    obtain ⟨w, tag⟩ := i
    dsimp only at hx
    subst hx
    cases tag <;> cases ha
  · subst h
    refine hnext fun x l hx => ?_
    obtain ⟨w, tag⟩ := i
    dsimp only at hx
    subst hx
    cases tag <;> cases ha
  · subst h
    refine hnext fun x l hx => ?_
    obtain ⟨w, tag⟩ := i
    dsimp only at hx
    subst hx
    cases tag <;> cases ha
  · obtain ⟨c, hc⟩ := lcond_of_armOf_cc ha
    obtain ⟨w, tag⟩ := i
    dsimp only at hc
    subst hc
    rcases h with ⟨rfl, -⟩ | ⟨p, hp, rfl⟩
    · simp [webSuccs]
    · simp [webSuccs, hp]
  · obtain ⟨x, hx⟩ := lgoto_of_armOf_goto ha
    obtain ⟨w, tag⟩ := i
    dsimp only at hx
    subst hx
    obtain ⟨p, hp, rfl⟩ := h
    simp [webSuccs, hp]
  · subst h
    refine hnext fun x l hx => ?_
    obtain ⟨w, tag⟩ := i
    dsimp only at hx
    subst hx
    cases tag <;> cases ha

/-- The successors of the coalescing check are successors of `webSuccs` in the tagged
    code. -/
theorem mem_webSuccs_tagA_of_succ {body : List LinstrRM} {k k' : Nat} {i : LinstrRM}
    (h : Succ body k i k') :
    k' ∈ webSuccs (body.map (renArr tagA)) k (renArr tagA i) := by
  rw [webSuccs_congr (renArr_ctl tagA i).2.1 (renArr_ctl tagA i).2.2
    (findLabelMem_map _ fun j _ => (renArr_ctl tagA j).1)]
  exact mem_webSuccs_of_succ h

/-! ## 2. Liveness under a certificate of the tagged code -/

/-- A tagged name that the tagged instruction writes is the array that the instruction
    writes. -/
def WriteSorted (i : LinstrRM) : Prop :=
  ∀ y, tagA y ∈ defNames (renArr tagA i).1 → arrWrite i = some y

/-- **A live name under a certificate of the tagged code.** For a code `body` of
    instructions that are no shadow instructions of a call and of `WriteSorted`, a
    certificate `D` of its tagged code at the names `E`, and names `obs` read after the code
    whose tagged names are in `D` at the end or in `E`: the tagged name of a name live at a
    position (`PLive`) is in `D` there or in `E`. -/
theorem pLive_tagA {E : String → Prop} {body : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E (body.map (renArr tagA)) D) (hn : ∀ i ∈ body, NoShadow i)
    (hw : ∀ i ∈ body, WriteSorted i) {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} {obs : List String}
    (ho : ∀ r ∈ obs, D body.length (tagA r) ∨ E (tagA r)) {k : Nat} {r : String}
    (h : PLive body aa ao obs k r) : D k (tagA r) ∨ E (tagA r) := by
  induction h with
  | obs hr => exact ho _ hr
  | @read k i y hi hr =>
      have hi' : (body.map (renArr tagA))[k]? = some (renArr tagA i) := by simp [hi]
      exact hC.use _ _ hi' _ (mem_useNames_renArr_arrReads tagA
        (mem_arrReads_of_rdArr (hn _ (List.mem_of_getElem? hi)) hr))
  | @step k k' i y hi hs hwr _ ih =>
      rcases ih with h1 | h1
      · have hi' : (body.map (renArr tagA))[k]? = some (renArr tagA i) := by simp [hi]
        rcases hC.step _ _ hi' _ (mem_webSuccs_tagA_of_succ hs) _ h1 with h2 | h2
        · exact Or.inl h2
        · refine absurd ?_ hwr
          rw [wrArr_eq_arrWrite (hn _ (List.mem_of_getElem? hi))]
          exact (hw _ (List.mem_of_getElem? hi) _ h2).symm
      · exact Or.inr h1

/-- A name live at the entry, under a certificate of the tagged code, has its tagged name
    among the names read without a prior write. -/
theorem pLive_entry_tagA {E : String → Prop} {body : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E (body.map (renArr tagA)) D) (hn : ∀ i ∈ body, NoShadow i)
    (hw : ∀ i ∈ body, WriteSorted i) {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} {obs : List String}
    (ho : ∀ r ∈ obs, D body.length (tagA r) ∨ E (tagA r)) {r : String}
    (h : PLive body aa ao obs 0 r) : E (tagA r) :=
  (pLive_tagA hC hn hw ho h).resolve_left (hC.entry _)

/-! ## 3. The written arrays of the code with the result copies -/

theorem writeSorted_of_sortPlain {i : LinstrRM} (h : SortPlain i) : WriteSorted i :=
  fun _ hy => arrWrite_of_tagA_mem_defNames h hy

theorem writeSorted_movI {dst : String} (hd : ¬ IsTag dst) (o : LOperand) :
    WriteSorted (movI dst o) := by
  intro y hy
  rw [renArr_movI] at hy
  simp only [movI, defNames_Lopn, JasminLsemExportRewrites.opNames, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.mem_singleton] at hy
  exact absurd (hy ▸ isTag_tagA y) hd

theorem notTag_copyIdx : ¬ IsTag copyIdx := notTag_of_head (c := 'r') (by decide) (by decide)

theorem notTag_copyTmp : ¬ IsTag copyTmp := notTag_of_head (c := 'r') (by decide) (by decide)

theorem writeSorted_resCopyCode (src D : String) (m : Nat) :
    ∀ i ∈ resCopyCode src D m, WriteSorted i := by
  intro i hi
  obtain ⟨j, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact writeSorted_movI notTag_copyIdx _
  · intro y hy
    simp only [renArr, X86Backend.ImageCoalesceCfg.renLoad, ↓reduceIte, defNames_Lopn,
      JasminLsemExportRewrites.opNames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_singleton] at hy
    exact absurd (hy ▸ isTag_tagA y) notTag_copyTmp
  · intro y hy
    simp only [renArr, X86Backend.ImageCoalesceCfg.renStore, ↓reduceIte, defNames_Lopn,
      JasminLsemExportRewrites.opNames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_singleton, tagA_injective.eq_iff] at hy
    subst hy
    simp [arrWrite, storeStruct?]

/-! ## 4. The names the code with the result copies assigns -/

/-- The register an instruction assigns is a name it writes. -/
theorem mem_defNames_of_lopnDst {w : LinstrR} {x : String} (h : lopnDst w = some x) :
    x ∈ defNames w := by
  unfold lopnDst at h
  split at h
  · cases h
    simp [defNames_Lopn, JasminLsemExportRewrites.opNames]
  · cases h

theorem head_argName (j : Nat) : (argName j).toList.head? = some 'a' := by
  simp [argName, String.toList_append]

theorem not_exportRegName_argName (j : Nat) : ¬ ExportRegName (argName j) := by
  unfold ExportRegName
  rw [head_argName]
  simp

/-- A general-purpose name is no argument name. -/
theorem argName_ne_of_gpOk {x : String} (h : gpOk x = true) (j : Nat) : x ≠ argName j := by
  rintro rfl
  have hall : ∀ s ∈ gpList, s.toList.head? = some 'R' := by decide
  have hm : argName j ∈ gpList := by simpa [gpOk] using h
  have := hall _ hm
  rw [head_argName] at this
  simp at this

theorem copyName_succ_ne_argName (k j j' : Nat) :
    copyName (argName j') (k + 1) ≠ argName j := by
  intro h
  have h' := congrArg String.toList h
  simp only [copyName, argName, Nat.add_one_ne_zero, ite_false, String.toList_append] at h'
  have h2 : '#' ∈ Nat.toDigits 10 j := by
    have := List.append_cancel_left (as := ['a']) (by simpa using h')
    rw [← this]
    simp
  simpa using Nat.isDigit_of_mem_toDigits (by decide) (by decide) h2

theorem copyIdx_ne_argName (j : Nat) : copyIdx ≠ argName j := by
  intro h
  have := congrArg (fun s => s.toList.head?) h
  simp only [head_argName] at this
  revert this
  decide

theorem copyTmp_ne_argName (j : Nat) : copyTmp ≠ argName j := by
  intro h
  have := congrArg (fun s => s.toList.head?) h
  simp only [head_argName] at this
  revert this
  decide

/-- **The code with the result copies of an export assigns no argument name**, when the
    export name of the result register of the layout is a general-purpose name. -/
theorem regionCoCode_lopnDst_ne_argName (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) {d n : Nat} {r : Exported}
    (h : exportR nArgs fn p d n x86Data = some r) (σ : AbiLayout) (nm : String → String)
    (t : JasminTy) (hgp : ∀ RA, σ.result = .reg RA → gpOk (nm RA) = true)
    (callee : Option CalleeTab) :
    ∀ i ∈ regionCoCode σ nm t r.code r.res (regionCopy σ nm t callee r.code r.res),
      ∀ j, lopnDst i.1 ≠ some (argName j) := by
  have hcode : ∀ i ∈ r.code, ∀ j, lopnDst i.1 ≠ some (argName j) := fun i hi j hd =>
    not_exportRegName_argName j (exportR_defNames nArgs fn p d n r h i hi _
      (mem_defNames_of_lopnDst hd))
  have hmov : ∀ i ∈ movesOf (regionRet σ nm t r.res).toList, ∀ j,
      lopnDst i.1 ≠ some (argName j) := by
    intro i hi j hd
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
    simp only [lopnDst, JasminLsemExportLower.movWire, Option.some.injEq] at hd
    change q ∈ (regionRet σ nm t r.res).toList at hq
    unfold regionRet at hq
    split at hq
    · split at hq
      · rename_i RA op hres _
        simp only [Option.toList_some, List.mem_singleton] at hq
        subst hq
        exact argName_ne_of_gpOk (hgp RA hres) j hd
      · cases hq
    · cases hq
  intro i hi j
  unfold regionCoCode at hi
  split at hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact hcode i hi j
    · exact hmov i hi j
  · rename_i src D m hcp
    rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact hcode i hi j
      · exact hmov i hi j
    · obtain ⟨-, -, -, ⟨j', -, -, -, rfl⟩, -, -⟩ := regionCopy_some hcp
      obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hi
      simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simp only [lopnDst, movImmI, movI, ne_eq,
        Option.some.injEq]
      · exact copyIdx_ne_argName j
      · exact copyTmp_ne_argName j
      · exact copyName_succ_ne_argName k j j'

/-! ## 5. The certificate of the tagged code with the names read after it -/

theorem notTag_of_gpOk {x : String} (h : gpOk x = true) : ¬ IsTag x := by
  have hall : ∀ s ∈ gpList, s.toList.head? = some 'R' := by decide
  exact notTag_of_head (hall x (by simpa [gpOk] using h)) (by decide)

/-- **The certificate of the tagged code with the result copies, at the names read after
    it.** The certificate `cert_regionCoCodeS` of the tagged code of `regionCoCode` with its
    result copy, which holds at the end the tagged names of the array names read after the
    code (`regionCoObs`), or those tagged names are argument names. -/
theorem cert_regionCoCodeS_obs (fn : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) (σ : AbiLayout)
    (nm : String → String) (hsym : ∀ i ∈ r.code, symReads i = [])
    (hlen : Γ.length ≤ σ.args.length) :
    ∃ D, Cert (ArgS σ.args.length)
      ((regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)).map
        (renArr tagA)) D ∧
      ∀ x ∈ regionCoObs t (regionOut (regionCopy σ nm t none r.code r.res) r.res),
        D (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)).length
          (tagA x) ∨ ArgS σ.args.length (tagA x) := by
  have hns := RegionCoComplete.exportR_noShadow RegionCoComplete.x86Data_guardsNoShadow _ _ p
    hp hc _ _ r h
  have hEA : ∀ y, ExportES Γ.length (r.code.map (renArr tagA)) y → ArgS σ.args.length y := by
    rintro y (⟨j, hj, hy⟩ | ⟨i, hi, hy⟩)
    · exact ⟨j, by omega, hy⟩
    · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
      rw [symReads_renArr (hns i' hi'), hsym i' hi'] at hy
      cases hy
  obtain ⟨D0, hC0, hres0⟩ := exportR_certS fn p hp hc h
  have hC1 := hC0.monoE hEA
  have hres : ∀ q ∈ [t].zip r.res, D0 r.code.length (sortName q.1 (operandName q.2))
      ∨ ArgS σ.args.length (sortName q.1 (operandName q.2)) :=
    fun q hq => (hres0 q hq).imp_right (hEA _)
  let L := (regionRet σ nm t r.res).toList
  have hmovs : movesOf L = L.map fun q => movI q.2 (.reg q.1) := rfl
  obtain ⟨D1, hC2, hD1⟩ : ∃ D1, Cert (ArgS σ.args.length)
      (r.code.map (renArr tagA) ++ movesOf L) D1
      ∧ ∀ x, D0 (r.code.map (renArr tagA)).length x →
        D1 (r.code.map (renArr tagA) ++ movesOf L).length x := by
    refine hC1.append_blk (Λ := fun _ _ => False) ?_ (JasminLsemRenameLoop.movesOf_isLopn _)
    rw [hmovs]
    refine (blk_movs (fun q => q.2) (fun q => .reg q.1) L
      (X := D0 (r.code.map (renArr tagA)).length) (fun q hq x hx => ?_)).mono (fun _ h => h)
      (fun x hx => Or.inl hx)
    simp only [JasminLsemExportRewrites.opNames, List.mem_singleton] at hx
    subst hx
    change q ∈ (regionRet σ nm t r.res).toList at hq
    unfold regionRet at hq
    split at hq
    · split at hq
      · rename_i op _ hr1
        simp only [Option.toList_some, List.mem_singleton] at hq
        subst hq
        have := hres (_, op) (by rw [hr1]; exact List.mem_singleton_self _)
        rw [sortName_of_reg rfl] at this
        rwa [List.length_map]
      · cases hq
    · cases hq
  have hmapM : (movesOf L).map (renArr tagA) = movesOf L := by
    rw [hmovs, map_renArr_movs]
  have hlenM : (r.code.map (renArr tagA) ++ movesOf L).length
      = (r.code ++ movesOf L).length := by simp
  unfold regionCoCode
  split
  · rename_i hcp
    refine ⟨D1, by rw [List.map_append, hmapM]; exact hC2, fun x hx => ?_⟩
    rw [hcp] at hx
    simp only [regionOut] at hx
    rw [← hlenM]
    unfold regionCoObs at hx
    split at hx
    · rename_i w m
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
      obtain ⟨op', hop'⟩ : ∃ op', r.res = [op'] :=
        List.length_eq_one_iff.mp (exportR_res_length _ fn p _ _ r h)
      rw [hop', List.mem_singleton] at hop
      subst hop
      have := hres (.stackArr w m, op) (by rw [hop']; exact List.mem_singleton_self _)
      rw [sortName_of_arr rfl] at this
      rcases this with h1 | h1
      · exact Or.inl (hD1 _ (by rwa [List.length_map]))
      · exact Or.inr h1
    · cases hx
  · rename_i src Dn m hcp
    obtain ⟨-, ht, ⟨op, hr1, hsrc⟩, ⟨j, q, hq, -, rfl⟩, -, -⟩ := regionCopy_some hcp
    have hjl : j < σ.args.length := (List.getElem?_eq_some_iff.mp hq).1
    have hs : D1 (r.code.map (renArr tagA) ++ movesOf L).length (tagA src)
        ∨ ArgS σ.args.length (tagA src) := by
      have := hres (t, op) (by rw [hr1]; exact List.mem_singleton_self _)
      rw [ht, sortName_of_arr rfl, ← ht, hsrc] at this
      rcases this with h1 | h1
      · exact Or.inl (hD1 _ (by rwa [List.length_map]))
      · exact Or.inr h1
    obtain ⟨D2, hC3, hZ⟩ := hC2.append_blk (Λ := fun _ _ => False)
      (blk_resCopyS src (argName j) m hs (Or.inr ⟨j, hjl, Or.inr rfl⟩) m)
      (isLopn_map_resCopyCode src (argName j) m)
    refine ⟨D2, by rw [List.map_append, List.map_append, hmapM]; exact hC3, fun x hx => ?_⟩
    rw [hcp] at hx
    simp only [regionOut, regionCoObs, ht, List.map_cons, List.map_nil, List.mem_singleton,
      operandName] at hx
    subst hx
    by_cases hm : m = 0
    · subst hm
      exact Or.inr ⟨j, hjl, Or.inr (by simp [copyName])⟩
    · left
      have := hZ _ (Or.inr ⟨Nat.pos_of_ne_zero hm, rfl⟩)
      refine cast (congrArg (fun n => D2 n (tagA (copyName (argName j) m))) ?_) this
      simp [L, resCopyCode]

/-! ## 6. The entry conjunct -/

/-- **The instructions of the code with the result copies write their tagged arrays.** -/
theorem writeSorted_regionCoCode (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) (σ : AbiLayout)
    (nm : String → String) (t : JasminTy) (hsym : ∀ i ∈ r.code, symReads i = [])
    (hgp : ∀ RA, σ.result = .reg RA → gpOk (nm RA) = true) (cp : Option (String × String × Nat)) :
    ∀ i ∈ regionCoCode σ nm t r.code r.res cp, WriteSorted i := by
  have hT : NoTag r.code := noTag_exportR fn p hp hc h hsym fun i hi x hx => by
    rcases exportR_defNames _ fn p _ _ r h i hi x hx with h1 | h1
    · exact notTag_of_head h1 (by decide)
    · exact notTag_of_head h1 (by decide)
  have hmov : ∀ i ∈ movesOf (regionRet σ nm t r.res).toList, WriteSorted i := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
    change q ∈ (regionRet σ nm t r.res).toList at hq
    unfold regionRet at hq
    split at hq
    · split at hq
      · rename_i RA op hres _
        simp only [Option.toList_some, List.mem_singleton] at hq
        subst hq
        exact writeSorted_movI (notTag_of_gpOk (hgp RA hres)) _
      · cases hq
    · cases hq
  intro i hi
  unfold regionCoCode at hi
  split at hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact writeSorted_of_sortPlain (hT i hi)
    · exact hmov i hi
  · rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact writeSorted_of_sortPlain (hT i hi)
      · exact hmov i hi
    · exact writeSorted_resCopyCode _ _ _ i hi

/-- **A name live at the entry of the code with the result copies is an argument name.** For
    the export `r` of a program over `Γ` of result type `t` without `call` that passes
    `regionExportableB`, from the depth and the argument count `Γ.length` and the label `0`
    on x86, at a layout with at least `Γ.length` parameters whose result register has a
    general-purpose export name: every array name live at the entry of the code with the
    result copies `regionCoCode`, when the names read after it are the returned array names
    `regionCoObs`, is an argument name of the layout. -/
theorem pLive_entry_argName (fn : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) (σ : AbiLayout)
    (nm : String → String) (hlen : Γ.length ≤ σ.args.length)
    (hgp : ∀ RA, σ.result = .reg RA → gpOk (nm RA) = true)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) {x : String}
    (hx : PLive (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)) aa ao
      (regionCoObs t (regionOut (regionCopy σ nm t none r.code r.res) r.res)) 0 x) :
    ∃ j, j < σ.args.length ∧ x = argName j := by
  have hsym := RegionAllocMapDom.exportR_symReads _ fn p hp hc h
  obtain ⟨D, hC, ho⟩ := cert_regionCoCodeS_obs fn p hp hc h σ nm hsym hlen
  have hns := RegionCoComplete.noShadow_regionCoCode σ nm t r.code r.res
    (regionCopy σ nm t none r.code r.res)
    (RegionCoComplete.exportR_noShadow RegionCoComplete.x86Data_guardsNoShadow _ _ p hp hc _ _ r h)
  obtain ⟨j, hj, hx'⟩ := pLive_entry_tagA hC hns
    (writeSorted_regionCoCode fn p hp hc h σ nm t hsym hgp _) ho hx
  rcases hx' with hx' | hx'
  · exact absurd (hx' ▸ isTag_tagA x) (notTag_argName j)
  · exact ⟨j, hj, tagA_injective hx'⟩

/-- **The entry conjunct of `StorageDisjoint`** on the code with the result copies of an
    export: under the conditions of `pLive_entry_argName`, no array name live at the entry is
    assigned by an instruction of the code. -/
theorem storageDisjoint_entry (fn : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) (σ : AbiLayout)
    (nm : String → String) (hlen : Γ.length ≤ σ.args.length)
    (hgp : ∀ RA, σ.result = .reg RA → gpOk (nm RA) = true)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    ∀ x, PLive (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)) aa ao
        (regionCoObs t (regionOut (regionCopy σ nm t none r.code r.res) r.res)) 0 x →
      ∀ i ∈ regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res),
        lopnDst i.1 ≠ some x := by
  intro x hx i hi
  obtain ⟨j, -, rfl⟩ := pLive_entry_argName fn p hp hc h σ nm hlen hgp aa ao hx
  exact regionCoCode_lopnDst_ne_argName _ fn p h σ nm t hgp none i hi j

/-- **On the code with the result copies of an export, `StorageDisjoint` is its first
    conjunct**: under the conditions of `pLive_entry_argName`, at every alias map `ρ`, the
    storage classes are disjoint exactly when no two distinct names of one class are in use at
    the same position. -/
theorem storageDisjoint_iff_classes (fn : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) (σ : AbiLayout)
    (nm : String → String) (hlen : Γ.length ≤ σ.args.length)
    (hgp : ∀ RA, σ.result = .reg RA → gpOk (nm RA) = true)
    (ρ : String → String) (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    let body := regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)
    let obs := regionCoObs t (regionOut (regionCopy σ nm t none r.code r.res) r.res)
    StorageDisjoint ρ body aa ao obs ↔
      ∀ k y y', RegionCoComplete.InUse body aa ao obs k y →
        RegionCoComplete.InUse body aa ao obs k y' → ρ y = ρ y' → y = y' :=
  ⟨fun hs => hs.1, fun hs => ⟨hs, storageDisjoint_entry fn p hp hc h σ nm hlen hgp aa ao⟩⟩

/-! ## 7. The class and coalescing stages on the export -/

/-- **No real aliasing on the export from disjoint classes** (`exportR_noRealAlias_of_classes`).
    Under the conditions of `pLive_entry_argName`, when no two distinct array names of one
    storage class of the alias map `regionAliasTab` are in use at the same position of the
    code with the result copies, that alias map has no real aliasing on that code. -/
theorem exportR_noRealAlias_of_classes (fn : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) (σ : AbiLayout)
    (nm : String → String) (hlen : Γ.length ≤ σ.args.length)
    (hgp : ∀ RA, σ.result = .reg RA → gpOk (nm RA) = true)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat)
    (hcls : ∀ k y y',
      InUse (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)) aa ao
        (regionCoObs t (regionOut (regionCopy σ nm t none r.code r.res) r.res)) k y →
      InUse (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)) aa ao
        (regionCoObs t (regionOut (regionCopy σ nm t none r.code r.res) r.res)) k y' →
      canonMemrefName (regionAliasTab σ nm t none r.res
          (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res))) y =
        canonMemrefName (regionAliasTab σ nm t none r.res
          (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res))) y' →
      y = y') :
    NoRealAlias (canonMemrefName (regionAliasTab σ nm t none r.res
        (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res))))
      (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)) aa ao
      (regionCoObs t (regionOut (regionCopy σ nm t none r.code r.res) r.res)) :=
  noRealAlias_of_storageDisjoint
    ((storageDisjoint_iff_classes fn p hp hc h σ nm hlen hgp _ aa ao).mpr hcls)

/-- **The class and coalescing stages accept the export from disjoint classes.** For the
    export `r` of a program over `Γ` of result type `t` without `call` that passes
    `regionExportableB`, from the depth and the argument count `Γ.length` and the label `0`
    on x86, at a layout with at least `Γ.length` parameters whose result register has a
    general-purpose export name, when no two distinct array names of one storage class of
    `regionAliasTab` are in use at the same position of the code with the result copies,
    `regionCoStage` on the call-free arm refuses neither at `coClass`, nor at `coCfgB`, nor
    at `coEntryFix`, at every printed body, certificate and function name. -/
theorem regionCoStage_accept_of_classes (fn : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) (σ : AbiLayout)
    (nm : String → String) (hlen : Γ.length ≤ σ.args.length)
    (hgp : ∀ RA, σ.result = .reg RA → gpOk (nm RA) = true)
    (hcls : ∀ k y y',
      InUse (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res))
        (calleeAAT none) (calleeAOT none)
        (regionCoObs t (regionOut (regionCopy σ nm t none r.code r.res) r.res)) k y →
      InUse (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res))
        (calleeAAT none) (calleeAOT none)
        (regionCoObs t (regionOut (regionCopy σ nm t none r.code r.res) r.res)) k y' →
      canonMemrefName (regionAliasTab σ nm t none r.res
          (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res))) y =
        canonMemrefName (regionAliasTab σ nm t none r.res
          (regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res))) y' →
      y = y')
    (body : Lcmd) (cert : List (String × String)) (fn' : String) :
    regionCoStage σ nm body t r.code r.res cert none fn' ≠ some "coClass" ∧
      regionCoStage σ nm body t r.code r.res cert none fn' ≠ some "coCfgB" ∧
      regionCoStage σ nm body t r.code r.res cert none fn' ≠ some "coEntryFix" :=
  ⟨RegionExportForms.regionCoStage_ne_coClass h σ nm body t cert fn',
    regionCoStage_coalesce_of σ nm body t r.code r.res cert none fn'
      (exportR_tagOK _ fn x86Data p _ _ r h)
      (fun _ => exportR_noShadow x86Data_guardsNoShadow _ fn p hp hc _ _ r h)
      (exportR_noRealAlias_of_classes fn p hp hc h σ nm hlen hgp _ _ hcls)⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoStorage
