/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomStoreChain
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomResult

/-!
# The observed arrays are names of the coalesced code on the field domain

The stage `coResultName` of the region gate asks that the alias of each array read after the
code is a name of the coalesced code. On the field domain the program the export receives has
the shape `LoadsChainS`, so its export writes the array it returns
(`loadsChainS_export_class`), and the renaming by webs keeps a written returned name. Without
the result copy the array read after the code is the returned array, written by an instruction
whose coalesced form writes its alias; with the copy it is the last version of the result
buffer, which the last store of the copy writes. An array written by an instruction with a
plain tag has its alias among the names of the renamed instruction
(`contains_loopNames_of_wrArr`).

## Main results

* `loadsChainS_export_class`: the export of a program of the shape `LoadsChainS` is classified
  by `ExportClass` and returns one operand naming an array it writes.
* `coResultName_of_written`: the condition of the stage from a returned array that the code
  writes.
* `fieldDom_coResultName`: the stage `G5` on the field domain.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO zeroDst?
  arrWrite)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (ReadAt WrAt ConsumedAt
  ChainShape rdArr wrArr wrArrA armOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (loopNames)
open CatCrypt.Crypto.Hax (HaxModule)

/-! ## 1. The export of a program with a store -/

section Export

variable {nArgs : Nat} {fn : String}

/-- **The export of a program of the shape `LoadsChainS` writes an array.** -/
theorem loadsChainS_export_writes {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) (hn : nArgs ≤ Γ.length) {n : Nat}
    {r : Exported} (hr : exportR nArgs fn p Γ.length n = some r) :
    ∃ w d, WrAt r.code (fun _ => none) w d := by
  induction h generalizing n r with
  | @free Γ t ts e k he hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, -⟩ := bindOps_memFree_class nArgs Γ.length e he
      have hcode : (Exported.prepend (bindOps nArgs e Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      obtain ⟨w, d, hW⟩ := ih (by simp only [List.length_cons]; omega) hk'
      exact ⟨w + 1, d, wrAt_cons_succ.mpr hW⟩
  | @load Γ w m ts a i k hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, -⟩ := bindOps_load_class nArgs Γ.length a i
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackLoad w m, rfl,
          .cons a (.cons i .nil)⟩ : Expr jasminDialect Γ (.reg w)) Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      obtain ⟨w', d, hW⟩ := ih (by simp only [List.length_cons]; omega) hk'
      exact ⟨w' + 1, d, wrAt_cons_succ.mpr hW⟩
  | @store Γ w m ts v i x k hk =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, -, -, -, hwr, -⟩ := bindOps_store_class nArgs Γ.length v i x
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackStore w m, rfl,
          .cons v (.cons i (.cons x .nil))⟩ : Expr jasminDialect Γ (.stackArr w m)) Γ.length)
            rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      exact ⟨0, _, wrAt_cons_zero.mpr hwr⟩

/-- **The classification of the export of a program of the shape `LoadsChainS`**: its
    instructions are classified by `ExportClass` from a root, and it returns one operand naming
    an array it writes. -/
theorem loadsChainS_export_class {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChainS p) (hn : nArgs ≤ Γ.length) {n : Nat}
    {r : Exported} (hr : exportR nArgs fn p Γ.length n = some r) :
    (∃ x, ExportClass r.code x) ∧ ∃ y, r.res.map operandName = [y] ∧
      ∃ w, WrAt r.code (fun _ => none) w y := by
  obtain ⟨x, -, -, -, hE, hR⟩ := loadsChain_export_class (fn := fn) h.loadsChain hn hr
  refine ⟨⟨x, hE⟩, ?_⟩
  rcases hR with hn0 | hy
  · obtain ⟨w, d, hW⟩ := loadsChainS_export_writes (fn := fn) h hn hr
    exact absurd hW (hn0 w d)
  · exact hy

end Export

/-! ## 2. Written arrays are names of the renamed code -/

/-- The destination of a store wire is a name of the wire. -/
theorem storeStruct?_mem_instrNames {wire : LinstrR} {q : String × String × String × String}
    (h : JasminLsemMem.storeStruct? wire = some q) : q.1 ∈ instrNames wire := by
  unfold JasminLsemMem.storeStruct? at h
  split at h
  · split at h
    · cases h
      simp [instrNames, JasminLsemExportRewrites.opNames]
    · cases h
  · cases h

/-- The destination of a zeroing wire is a name of the wire. -/
theorem zeroStruct?_mem_instrNames {wire : LinstrR} {d : String}
    (h : JasminLsemMem.zeroStruct? wire = some d) : d ∈ instrNames wire := by
  unfold JasminLsemMem.zeroStruct? at h
  split at h
  · split at h
    · cases h
      simp [instrNames, JasminLsemExportRewrites.opNames]
    · cases h
  · cases h

/-- The destination of a constant-index store wire is a name of the wire. -/
theorem storeImmStruct?_mem_instrNames {wire : LinstrR} {q : String × String × String × Nat}
    (h : JasminLsemMem.storeImmStruct? wire = some q) : q.1 ∈ instrNames wire := by
  unfold JasminLsemMem.storeImmStruct? at h
  split at h
  · split at h
    · cases h
      simp [instrNames, JasminLsemExportRewrites.opNames]
    · cases h
  · cases h

/-- The array of an array write is a name of the instruction. -/
theorem arrWrite_mem_instrNames {i : LinstrRM} {d : String} (h : arrWrite i = some d) :
    d ∈ instrNames i.1 := by
  obtain ⟨wire, tag⟩ := i
  cases tag <;> simp only [arrWrite, Option.map_eq_some_iff] at h
  all_goals first
    | (cases h; done)
    | exact zeroStruct?_mem_instrNames h
    | (obtain ⟨q, hq, rfl⟩ := h
       first
         | exact storeStruct?_mem_instrNames hq
         | exact storeImmStruct?_mem_instrNames hq)

/-- An array an instruction writes is a name of the instruction. -/
theorem wrArr_mem_instrNames {i : LinstrRM} {d : String}
    (h : wrArr (fun _ => none) i = some d) : d ∈ instrNames i.1 := by
  obtain ⟨wire, tag⟩ := i
  unfold wrArr wrArrA at h
  split at h
  · simp at h
  · exact arrWrite_mem_instrNames h
  · exact arrWrite_mem_instrNames h
  · simp at h

/-- **The alias of an array written by an instruction with a plain tag is a name of the
    code renamed at its array positions.** -/
theorem contains_loopNames_of_wrArr (ρ : String → String) {C : List LinstrRM} {i : LinstrRM}
    {A : String} (hi : i ∈ C) (hp : PlainTag i) (hw : wrArr (fun _ => none) i = some A) :
    (loopNames (C.map (renArr ρ))).contains (ρ A) = true := by
  have h1 := (rdArr_wrArr_renArr ρ i hp).2
  rw [hw] at h1
  have h2 := wrArr_mem_instrNames h1
  unfold loopNames
  rw [List.contains_iff_mem]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨renArr ρ i, List.mem_map_of_mem hi, h2⟩)

/-- A renaming at array positions keeps a plain tag. -/
theorem plainTag_renArr (ρ : String → String) {i : LinstrRM} (h : PlainTag i) :
    PlainTag (renArr ρ i) := by
  obtain ⟨wire, tag⟩ := i
  cases tag <;> simp_all [renArr, PlainTag]

/-! ## 3. The condition of the stage -/

/-- **The condition of the stage `coResultName` from a written returned array**: on code with
    plain tags, without a register result, returning one operand naming an array it writes,
    and with a result copy of at least one word when one is taken, the alias of each array read
    after the code is a name of the coalesced code. -/
theorem coResultName_of_written {σ : AbiLayout} {nm : String → String} {t : JasminTy}
    {C : List LinstrRM} {res : List LOperand}
    (hplain : ∀ i ∈ C, PlainTag i) (hret : regionRet σ nm t res = none)
    (hW : ∃ y, res.map operandName = [y] ∧ ∃ w, WrAt C (fun _ => none) w y)
    (hm : ∀ src D m, regionCopy σ nm t none C res = some (src, D, m) → 0 < m) :
    (regionCoObs t (regionOut (regionCopy σ nm t none C res) res)).all (fun A =>
      (loopNames (regionCoBody σ nm t C res none)).contains
        (canonMemrefName (regionAliasTab σ nm t none res
          (regionCoCode σ nm t C res (regionCopy σ nm t none C res))) A)) = true := by
  unfold regionCoBody
  rw [List.all_eq_true]
  intro A hA
  cases hcp : regionCopy σ nm t none C res with
  | none =>
      rw [hcp] at hA
      obtain ⟨y, hy, w, i, hi, hw⟩ := hW
      have hA' : A = y := by
        have := regionCoObs_sub t res A hA
        rw [hy, List.mem_singleton] at this
        exact this
      subst hA'
      have hC : regionCoCode σ nm t C res none = C := by
        simp [regionCoCode, hret, JasminLsemRenameLoop.movesOf]
      rw [hC]
      exact contains_loopNames_of_wrArr _ (List.mem_of_getElem? hi)
        (hplain i (List.mem_of_getElem? hi)) hw
  | some c =>
      obtain ⟨src, D, m⟩ := c
      have hm0 := hm src D m hcp
      obtain ⟨-, rfl, -⟩ := regionCopy_some hcp
      rw [hcp] at hA
      simp only [regionOut, regionCoObs, List.map_cons, List.map_nil, List.mem_singleton,
        operandName] at hA
      subst hA
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      refine contains_loopNames_of_wrArr _ (i := (.Lopn [.reg (copyName D (m' + 1))] "STOREIDX"
        [.arrIdx (copyName D m') copyIdx 8, .reg copyTmp], .store 64 (m' + 1))) ?_ trivial ?_
      · simp only [regionCoCode, hret, Option.toList_none, JasminLsemRenameLoop.movesOf,
          List.map_nil, List.append_nil, List.mem_append]
        right
        simp only [resCopyCode, List.mem_flatMap, List.mem_range]
        exact ⟨m', by omega, by simp [resCopyStep]⟩
      · rfl

/-! ## 4. The stage `G5` -/

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- The gate does not refuse at `coResultName` when the alias of each observed array is a name
    of the coalesced code. -/
theorem regionCoStage_ne_coResultName {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String}
    (h : (regionCoObs t (regionOut (regionCopy σ nm t none (calleeCodeT none code) res)
      res)).all (fun A =>
      (loopNames (regionCoBody σ nm t (calleeCodeT none code) res none)).contains
        (canonMemrefName (regionAliasTab σ nm t none res
          (regionCoCode σ nm t (calleeCodeT none code) res
            (regionCopy σ nm t none (calleeCodeT none code) res))) A)) = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "coResultName" := by
  unfold regionCoStage
  dsimp only
  rw [h]
  simp only [Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- **The layout of a member of the field domain has at least one word.** -/
theorem fieldDomB_layout_pos (h : fieldDomB e σ = true) :
    ∃ k n, (k = 1 ∨ k = 2) ∧ σ.args = (FieldRoute.fieldAbi k n).args
      ∧ σ.result = .words "%rdi" n ∧ 0 < n := by
  obtain ⟨k, n, hk, ha, hr⟩ := fieldDomB_layout h
  refine ⟨k, n, hk, ha, hr, ?_⟩
  unfold fieldDomB at h
  split at h
  · rename_i k' n' hE
    obtain ⟨m, p, -, h64, -, hn, -⟩ := fieldDomE_wide hE
    have hp2 : 2 ≤ p := le_trans (Nat.one_lt_two_pow (by decide : (64 : Nat) ≠ 0)) h64
    have hpos : 0 < n' := hn ▸ fieldLimbs_pos hp2
    simp only [fieldAbiB, Bool.and_eq_true, decide_eq_true_eq] at h
    have hargs := h.1.1.1.1.1
    rw [ha] at hargs
    have h0 := congrArg (fun l : List AbiArg => (l.head?.map AbiArg.kind)) hargs
    rcases hk with rfl | rfl <;>
      simp [FieldRoute.fieldAbi, List.range_succ] at h0 <;> omega
  · cases h

open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webLook webRen webB webB_obs
  webB_exit)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom (exportR_mnemDom
  shadowCall?_of_shapeB)

/-- **The renaming by webs keeps a written returned name**: at a position map of web tables
    that `webB` accepts with the returned names among the names it checks after the body, the
    renamed code writes the returned name. -/
theorem written_webRen (tab : X86Backend.ArrWebs.WebSt × Std.HashSet Nat × Std.HashSet Nat)
    {L : Nat → List String} {obsW : List String} {C : List LinstrRM} {res : List LOperand}
    (hacc : webB (webLook tab) C L obsW (fun _ _ => none) (fun _ => none) = true)
    (hst : ∀ (k : Nat) (i : LinstrRM), C[k]? = some i → StraightOp i)
    (hplain : ∀ i ∈ C, PlainTag i)
    (hssa : ∀ k₁ k₂ d, WrAt C (fun _ => none) k₁ d → WrAt C (fun _ => none) k₂ d → k₁ = k₂)
    (hobs : ∀ y ∈ res.map operandName, y ∈ obsW)
    (hW : ∃ y, res.map operandName = [y] ∧ ∃ w, WrAt C (fun _ => none) w y) :
    ∃ y, res.map operandName = [y] ∧
      ∃ w, WrAt (webRen (webLook tab) (fun _ => none) C) (fun _ => none) w y := by
  obtain ⟨y, hy, w, hW⟩ := hW
  refine ⟨y, hy, w, ?_⟩
  have hyobs : y ∈ res.map operandName := by rw [hy]; exact List.mem_singleton_self _
  have hw' := wrAt_webRen_of (w := webLook tab) hplain hW
  have hwl : w < C.length := by
    obtain ⟨i, hi, -⟩ := hW
    exact (List.getElem?_eq_some_iff.mp hi).1
  have hc := webB_const' hacc hst (a := w + 1) (r := y) C.length (by omega) le_rfl
    (webB_obs hacc y (hobs y hyobs)) (fun j' i' hj' _ hi' hw'' => by
      have := hssa j' w y ⟨i', hi', hw''⟩ hW
      omega)
  rw [hc.2, webB_exit hacc y (hobs y hyobs)] at hw'
  exact hw'

/-- **Stage `G5` on the field domain**: the gate does not refuse at `coResultName`. -/
theorem fieldDom_coResultName (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coResultName" := by
  refine regionCoStage_ne_coResultName ?_
  have hret : ∀ res, regionRet σ exportReg t res = none := by
    obtain ⟨-, R, n, hR⟩ := fieldDomB_abi h
    exact fun _ => regionRet_words hR
  obtain ⟨k, n, hk, ha, -, hn0⟩ := fieldDomB_layout_pos h
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, hr, -, -, rfl⟩ := hB
  have ht : NarrowWords.wideTy t0 = .stackArr 64 n := by
    rw [fieldDom_chainTy h hq hk ha]
    rfl
  have hm : ∀ (C : List LinstrRM) (res : List LOperand) src D m,
      regionCopy σ exportReg (NarrowWords.wideTy t0) none C res = some (src, D, m) → 0 < m := by
    intro C res src D m hcp
    obtain ⟨-, htm, -⟩ := regionCopy_some hcp
    rw [ht] at htm
    injection htm with _ hnm
    omega
  have hL := fieldDom_legalize_loadsChainS h hq hq'
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal h) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hcf : (legalizeRegion q').callFree = true :=
    legalizeRegion_callFree ((NarrowWords.callFree_narrowPrep hq').trans (fieldDom_callFree h hq))
  have hsh : ∀ i ∈ r0.code, LprogIsa.shadowCall? i.1 = none := fun i hi =>
    shadowCall?_of_shapeB (exportR_mnemDom _ _ _ (fieldDom_legalize hE1) hcf _ _ _ hr0 i hi).2.2
  obtain ⟨⟨x, hE⟩, hW⟩ := loadsChainS_export_class (fn := fname) hL le_rfl hr0
  have hplain : ∀ i ∈ r0.code, PlainTag i := fun i hi => by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    exact (hE k i hk).1
  have hcc : ∀ C : List LinstrRM, calleeCodeT none C = C := fun _ => rfl
  rw [hcc]
  rcases regionWebsAt_cases (regionWebsEx σ exportReg) r0 with he | ⟨tab, L, hacc, he⟩
  · rw [he] at hr
    subst hr
    exact coResultName_of_written hplain (hret _) hW (hm _ _)
  · rw [he] at hr
    subst hr
    obtain ⟨-, hWr, -⟩ := loadsChain_export (fn := fname) (aa := fun _ _ => none)
      (ao := fun _ => none) (fun _ _ => rfl) (fun _ => rfl) hL.loadsChain le_rfl hr0
    have hst : ∀ (k : Nat) (i : LinstrRM), r0.code[k]? = some i → StraightOp i := fun k i hk =>
      straightOp_of_lopn (hsh i (List.mem_of_getElem? hk)) (hE k i hk).2.1
    have hssa : ∀ k₁ k₂ d, WrAt r0.code (fun _ => none) k₁ d →
        WrAt r0.code (fun _ => none) k₂ d → k₁ = k₂ := fun k₁ k₂ d h₁ h₂ => by
      have := JasminLsemSimulation.regName_injective ((hWr k₁ d h₁).symm.trans (hWr k₂ d h₂))
      omega
    have hplain' : ∀ i ∈ webRen (webLook tab) (fun _ => none) r0.code, PlainTag i := by
      intro i hi
      obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hi
      rw [getElem?_webRen] at hc
      obtain ⟨i0, hi0, rfl⟩ := Option.map_eq_some_iff.mp hc
      exact plainTag_renArr _ (hplain i0 (List.mem_of_getElem? hi0))
    exact coResultName_of_written hplain' (hret _)
      (written_webRen tab hacc hst hplain hssa
        (fun y hy => by unfold regionWebsObs; exact List.mem_append_left _ hy) hW) (hm _ _)

example (S : FieldDomStages) : type_of% @S.coResultName :=
  fun h hB => fieldDom_coResultName (fieldDomB_of_fieldDomB' h) hB

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
