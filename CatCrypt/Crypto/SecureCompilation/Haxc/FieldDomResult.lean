/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomRenB

/-!
# The result check on the field domain

On a member of the field domain the program returns one array of `n` words, the length of the
output array of the layout (`fieldDom_chainTy`): the call of the tagged head reads the operands
of the entry context, whose types are arrays of `n` words. The result check `regionResultB`
reads the returned name under the coalescing renaming: with the result copy it is the last
version of the result buffer, which the renaming sends to the buffer; without it the copy
decision has found the root of the returned array to be the buffer.

## Main results

* `fieldDom_chainTy`: the result type of the chain on a member of the field domain.
* `fieldDom_resultLayout`, `fieldDom_regionResBuf`: the output array of the layout is the
  result buffer, at `%rdi`.
* `getD_foldl_of_noWrite`: the alias steps keep the image of a name no instruction writes.
* `fieldDom_exportFacts`: the exported code writes no argument name and returns one operand.
* `fieldDom_regionResultB`: the stage `G7` on the field domain.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.Hax (HaxModule)
open _root_.Hax.FieldTag (fieldLimbs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotArrOf)

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- The renaming of the array positions of an instruction that is no shadow of a call by the
    identity is the identity. -/
theorem renArr_id_of_noShadow {i : LinstrRM} (h : LprogIsa.shadowCall? i.1 = none) :
    X86Backend.ImageCoalesceCfg.renArr id i = i := by
  obtain ⟨w, t⟩ := i
  have hA : ∀ o, X86Backend.ImageCoalesceCfg.renOpA id o = o := by
    intro o
    cases o <;> rfl
  cases t <;> simp only [X86Backend.ImageCoalesceCfg.renArr, X86Backend.ImageCoalesceCfg.renLoad,
    X86Backend.ImageCoalesceCfg.renStore, X86Backend.ImageCoalesceCfg.renZero,
    X86Backend.ImageCoalesceCfg.renStoreImm, X86Backend.ImageCoalesceCfg.renCallW, id] at h ⊢ <;>
    first
      | (rw [h])
      | (split <;> (try split) <;> simp [List.map_congr_left (fun o _ => hA o)])

/-- The type of a variable of a context is a type of the context. -/
theorem mem_of_var {d : Dialect} : ∀ {Γ : Ctxt d} {s : d.Ty}, Ctxt.Var Γ s → s ∈ Γ
  | _, _, .here => List.mem_cons_self
  | _, _, .there v => List.mem_cons_of_mem _ (mem_of_var v)

/-- **The result type of the chain on a member of the field domain** is an array of `n` words,
    the length of the output array of the layout. -/
theorem fieldDom_chainTy {t0 : JasminTy} {q : NFProg jasminDialect (nfCtx σ) [t0]}
    (h : fieldDomB e σ = true)
    (hq : haxEntry.chainNF (HaxModule.single e) σ = some ⟨t0, q⟩) {k n : Nat}
    (hk : k = 1 ∨ k = 2) (ha : σ.args = (FieldRoute.fieldAbi k n).args) :
    t0 = .stackArr 64 n := by
  obtain ⟨T, p0, hp, -⟩ := fieldDom_haxToNF h
  obtain ⟨m, p, -, -, -, hT, hop⟩ := fieldDom_haxToNF_opRet h hp
  have hpn : fieldLimbs p = n := by
    obtain ⟨-, args, -⟩ := hop
    match args with
    | .cons v _ =>
      have hv := mem_of_var v
      rcases hk with rfl | rfl
      · rw [abiEntry_fieldAbi_one ha] at hv
        simpa [CatCrypt.Crypto.Hax.ImpToNF.entryCtx] using hv
      · rw [abiEntry_fieldAbi_two ha] at hv
        simpa [CatCrypt.Crypto.Hax.ImpToNF.entryCtx] using hv
  subst hT
  simp only [NFEntry.chainNF, haxEntry, hp, Option.bind_some, Option.map_eq_some_iff] at hq
  obtain ⟨q', -, heq⟩ := hq
  cases heq
  rw [hpn]
  rfl

/-! ## The layout of the result -/

/-- The layout facts of the output array of a member of the field domain. -/
theorem fieldDom_resultLayout {k n : Nat} (hk : k = 1 ∨ k = 2)
    (ha : σ.args = (FieldRoute.fieldAbi k n).args) :
    slotArrOf σ exportReg (JasminLsemAddrImage.slotOfReg (exportReg "%rdi")) = some (argName 0, n)
      ∧ X86Backend.DecodeGenNode.abiReg σ (argName 0) = some "%rdi" := by
  have e1 : exportReg "%rdi" = "RDI" := by decide
  rcases hk with rfl | rfl <;>
    simp [slotArrOf, X86Backend.DecodeGenNode.abiReg, X86Backend.DecodeGenNode.abiArgOf, ha,
      FieldRoute.fieldAbi, FieldRoute.fieldArgReg, List.range_succ, List.findIdx?, argName,
      e1, JasminLsemAddrImage.slotOfReg, List.findIdx?.go]

/-- The result buffer of a member of the field domain is the output array. -/
theorem fieldDom_regionResBuf {k n : Nat} (hk : k = 1 ∨ k = 2)
    (ha : σ.args = (FieldRoute.fieldAbi k n).args) (hr : σ.result = .words "%rdi" n) :
    regionResBuf σ exportReg = some (argName 0, n) := by
  unfold regionResBuf
  rw [hr]
  exact (fieldDom_resultLayout hk ha).1

/-- A member of the field domain has fewer than `2 ^ 64` words. -/
theorem fieldDomE_lt {k n : Nat} (h : fieldDomE e = some (k, n)) : n < 2 ^ 64 := by
  unfold fieldDomE at h
  split at h
  · split at h
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq,
        Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hc, -, rfl⟩ := h
      exact hc.2
    · cases h
  · cases h

/-! ## The alias table at a name no instruction writes -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (rdArr wrArr)

/-- **The alias steps keep the image of a name no instruction writes**, on code of the class
    `StoreClass`. -/
theorem getD_foldl_of_noWrite {x : String} :
    ∀ (L : List LinstrRM) (M : Std.HashMap String String), (∀ i ∈ L, StoreClass i) →
      (∀ i ∈ L, ∀ d, wrArr (fun _ => none) i = some d → d ≠ x) →
      (L.foldl (aliasStepO []) M).getD x x = M.getD x x
  | [], _, _, _ => rfl
  | i :: L, M, hc, hw => by
    rw [List.foldl_cons, getD_foldl_of_noWrite L _ (fun j hj => hc j (List.mem_cons_of_mem _ hj))
      (fun j hj => hw j (List.mem_cons_of_mem _ hj))]
    obtain ⟨hs, h1, h2⟩ := hc i List.mem_cons_self
    have hid := renArr_id_of_noShadow hs
    cases hwr : wrArr (fun _ => none) i with
    | none =>
      have := h1 hwr M id
      rw [hid] at this
      rw [this]
    | some d =>
      obtain ⟨b, -, hM⟩ := h2 d hwr
      have := hM M id
      rw [hid] at this
      rw [this, Std.HashMap.getD_insert]
      have hne : (d == x) = false := beq_eq_false_iff_ne.mpr (hw i List.mem_cons_self d hwr)
      simp [hne]

/-! ## The facts of the exported code of a member -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webLook webRen)

/-- **The exported code of a member of the field domain**: it has the facts `CodeFacts`, writes
    no argument name, and returns one operand whose name has no `#`. -/
theorem fieldDom_exportFacts (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    CodeFacts r.code
      ∧ (∀ i ∈ r.code, ∀ d, wrArr (fun _ => none) i = some d → ∀ j, d ≠ argName j)
      ∧ ∃ op, r.res = [op] ∧ '#' ∉ (JasminLsemWidthN.operandName op).toList := by
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, hr, -, -, rfl⟩ := hB
  have hL := fieldDom_legalize_loadsChain h hq hq'
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal h) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hcf : (legalizeRegion q').callFree = true :=
    legalizeRegion_callFree ((NarrowWords.callFree_narrowPrep hq').trans (fieldDom_callFree h hq))
  have hEx : regionExportableB (legalizeRegion q') = true := fieldDom_legalize hE1
  have hsh : ∀ i ∈ r0.code, LprogIsa.shadowCall? i.1 = none := fun i hi =>
    RegionAllocMapDom.shadowCall?_of_shapeB
      (RegionAllocMapDom.exportR_mnemDom _ _ _ hEx hcf _ _ _ hr0 i hi).2.2
  obtain ⟨hR, hW, -⟩ := loadsChain_export (fn := fname) (aa := fun _ _ => none)
    (ao := fun _ => none) (fun _ _ => rfl) (fun _ => rfl) hL le_rfl hr0
  have hres : r.res = r0.res := by rw [hr]; simp
  have hlen := ExportRegions.exportR_res_length _ _ _ _ _ _ hr0
  obtain ⟨op, hop⟩ := List.length_eq_one_iff.mp hlen
  have hop' : '#' ∉ (JasminLsemWidthN.operandName op).toList :=
    (hR r0.code.length _ (.inr ⟨rfl, by simp [hop]⟩)).hash_not_mem
  have hA : ∀ i ∈ r0.code, ∀ d, wrArr (fun _ => none) i = some d → ∀ j, d ≠ argName j := by
    intro i hi d hd j he
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    exact JasminLsemSimulation.regName_ne_argName _ j ((hW k d ⟨i, hk, hd⟩).symm.trans he)
  rcases regionWebsAt_cases (regionWebsEx σ exportReg) r0 with he | ⟨tab, L, hacc, he⟩
  · rw [he] at hr
    subst hr
    exact ⟨codeFacts_export hL le_rfl hr0 hsh, hA, op, hop, hop'⟩
  · rw [he] at hr
    subst hr
    refine ⟨codeFacts_webs tab hL le_rfl hr0 hsh hacc, fun i hi d hd j hdj => ?_, op, hop, hop'⟩
    obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hi
    have hplain : ∀ i ∈ r0.code, PlainTag i := fun i hi => by
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
      exact ((loadsChain_export_class (fn := fname) hL le_rfl hr0).choose_spec.2.2.2.1 k i hk).1
    obtain ⟨d0, hd0, rfl⟩ := wrAt_webRen hplain ⟨i, hc, hd⟩
    obtain ⟨i0, hi0, hw0⟩ := hd0
    have hhash : '#' ∉ d0.toList := by
      rw [hW c d0 ⟨i0, hi0, hw0⟩]
      exact hash_not_mem_regName _
    obtain rfl := webLook_eq_plain tab hhash (hash_not_mem_argName j) hdj
    exact hA i0 (List.mem_of_getElem? hi0) _ hw0 j rfl

/-! ## The stage `G7` -/

/-- The gate does not refuse at `regionResultB` when the result check accepts. -/
theorem regionCoStage_ne_regionResultB {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String}
    (h : regionResultB σ nm b t ((regionOut (regionCopy σ nm t none (calleeCodeT none code) res)
      res).map fun op => .reg (canonMemrefName (regionAliasTab σ nm t none res
        (regionCoCode σ nm t (calleeCodeT none code) res
          (regionCopy σ nm t none (calleeCodeT none code) res))) (JasminLsemWidthN.operandName op)))
      = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "regionResultB" := by
  unfold regionCoStage
  dsimp only
  rw [h]
  simp only [Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- **Stage `G7` on the field domain**: the gate does not refuse at the result check
    `regionResultB`. -/
theorem fieldDom_regionResultB (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "regionResultB" := by
  refine regionCoStage_ne_regionResultB ?_
  obtain ⟨hF, hA, op, hop, hoh⟩ := fieldDom_exportFacts h hB
  obtain ⟨t0, q, -, -, -, hq, -, -, -, -, -, rfl⟩ := hB
  obtain ⟨k, n, hk, ha, hres⟩ := fieldDomB_layout h
  have hn64 : n < 2 ^ 64 := by
    unfold fieldDomB at h
    split at h
    · rename_i k' n' hE
      have hlt := fieldDomE_lt hE
      simp only [fieldAbiB, Bool.and_eq_true, decide_eq_true_eq] at h
      have hargs := h.1.1.1.1.1
      rw [ha] at hargs
      have h0 := congrArg (fun l : List AbiArg => (l.head?.map AbiArg.kind)) hargs
      rcases hk with rfl | rfl <;>
        simp [FieldRoute.fieldAbi, List.range_succ] at h0 <;> omega
    · cases h
  have ht : NarrowWords.wideTy t0 = .stackArr 64 n := by
    rw [fieldDom_chainTy h hq hk ha]
    rfl
  have hbuf := fieldDom_regionResBuf hk ha hres
  obtain ⟨hslot, habi⟩ := fieldDom_resultLayout hk ha
  have hcls := hF.1
  have hD : ∀ M : Std.HashMap String String, (∀ x, M.getD x x = x ∨ M.getD x x = argName 0) →
      (r.code.foldl (aliasStepO []) M).getD (argName 0) (argName 0) = argName 0 := by
    intro M hM
    rw [getD_foldl_of_noWrite r.code M hcls fun i hi d hd => hA i hi d hd 0]
    rcases hM (argName 0) with h1 | h1 <;> exact h1
  rw [hop, ht]
  have hrr : resAliasOf none ((regionResBuf σ exportReg).map Prod.fst) [.stackArr 64 n] [op]
      = some (argName 0, JasminLsemWidthN.operandName op) := by
    rw [hbuf]
    simp [resAliasOf, RegionAllocMapDom.argName_ne_empty]
  have hrt : regionRet σ exportReg (.stackArr 64 n) [op] = none := by
    obtain ⟨-, R, n', hR⟩ := fieldDomB_abi h
    exact regionRet_words hR
  have hcc : calleeCodeT none r.code = r.code := rfl
  rw [hcc]
  -- the initial tables of the alias table with the result root
  have hM0 : ∀ (rt : String) (x : String),
      (({} : Std.HashMap String String).insert rt (argName 0)).getD x x = x
        ∨ (({} : Std.HashMap String String).insert rt (argName 0)).getD x x = argName 0 := by
    intro rt x
    rw [Std.HashMap.getD_insert]
    split
    · exact .inr rfl
    · exact .inl (by simp)
  have hE0 : ∀ x, ({} : Std.HashMap String String).getD x x = x ∨
      ({} : Std.HashMap String String).getD x x = argName 0 := fun x => .inl (by simp)
  cases hcp : regionCopy σ exportReg (.stackArr 64 n) none r.code [op] with
  | none =>
    have hno : X86Backend.ImageStraightRoute.chainAliasRes [] (argName 0)
        (JasminLsemWidthN.operandName op) r.code (JasminLsemWidthN.operandName op)
        = argName 0 := by
      unfold regionCopy at hcp
      rw [hbuf] at hcp
      simp only [resCopyOf] at hcp
      by_contra hne
      have hc : ((64 == 64 && argName 0 != "" && X86Backend.ImageStraightRoute.chainAliasRes []
          (argName 0) (JasminLsemWidthN.operandName op) r.code (JasminLsemWidthN.operandName op)
            != argName 0 && decide (n < 2 ^ 64) && (List.range n).all fun j =>
              JasminLsemWidthN.operandName op != copyName (argName 0) (j + 1)) = true) := by
        simp only [Bool.and_eq_true, beq_self_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
          List.all_eq_true, List.mem_range, true_and]
        exact ⟨⟨⟨RegionAllocMapDom.argName_ne_empty 0, hne⟩, hn64⟩, fun j _ =>
          ne_copyName_of_hash hoh _ j⟩
      rw [ite_eq_left hc] at hcp
      simp at hcp
    simp only [regionOut, regionCoCode, hrt, Option.toList_none, JasminLsemRenameLoop.movesOf,
      List.map_nil, List.append_nil, List.map_cons, regionAliasTab, resAliasTab, hrr]
    change regionResultB σ exportReg b (.stackArr 64 n) [.reg (X86Backend.ImageStraightRoute.chainAliasRes
      [] (argName 0) (JasminLsemWidthN.operandName op) r.code (JasminLsemWidthN.operandName op))]
      = true
    rw [hno]
    simp [regionResultB, hres, habi, hslot, JasminLsemWidthN.operandName]
  | some c =>
    obtain ⟨src, D, m⟩ := c
    have hDm : D = argName 0 ∧ m = n := by
      unfold regionCopy at hcp
      rw [hbuf] at hcp
      simp only [Option.filter_eq_some_iff, beq_iff_eq] at hcp
      exact ⟨RegionAllocMapPins.resCopyOf_buf hcp.1, hcp.2⟩
    obtain ⟨rfl, rfl⟩ := hDm
    have key : ∀ M : Std.HashMap String String, (∀ x, M.getD x x = x ∨ M.getD x x = argName 0) →
        canonMemrefName ((r.code ++ resCopyCode src (argName 0) m).foldl (aliasStepO []) M)
          (copyName (argName 0) m) = argName 0 := by
      intro M hM
      unfold canonMemrefName
      rw [List.foldl_append, getD_foldl_resCopyCode]
      split
      · exact hD M hM
      · rename_i hno
        cases m with
        | zero =>
          have h0 : copyName (argName 0) 0 = argName 0 := by simp [copyName]
          rw [h0]
          exact hD M hM
        | succ m => exact absurd ⟨m, by omega, rfl⟩ hno
    have hroot : canonMemrefName (regionAliasTab σ exportReg (.stackArr 64 m) none [op]
        (regionCoCode σ exportReg (.stackArr 64 m) r.code [op] (some (src, argName 0, m))))
        (copyName (argName 0) m) = argName 0 := by
      simp only [regionAliasTab, resAliasTab, hrr, regionCoCode, hrt, Option.toList_none,
        JasminLsemRenameLoop.movesOf, List.map_nil, List.append_nil]
      unfold X86Backend.ImageStraightRoute.aliasTabRes
      split
      · exact key _ (hM0 _)
      · exact key _ hE0
    simp only [regionOut, List.map_cons, List.map_nil, JasminLsemWidthN.operandName]
    rw [hroot]
    simp [regionResultB, hres, habi, hslot, JasminLsemWidthN.operandName]

example (S : FieldDomStages) : type_of% @S.regionResultB := @fieldDom_regionResultB

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
