/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomPosClass

/-!
# Array self-moves of the reference

The hypothesis `hNP` of `fieldDom_foldPos_of_loadsChainK` asks that the code `pre ++ merged`
of the parts has no pair of `selfPairB` behind the prefix. This module reduces it to the
exported code. The renamings of the parts (`renArr` of the coalescing, `renRM` of the pairs
and of the merge) keep the shape of a load and of a store, so a pair of an array self-move of
`merged` is a load directly followed by a store of the code with its result copies. The moves
of the result copy have no such pair, and in the result copy `resCopyCode` a load is directly
followed by a store whose base is a version of the result buffer.

## Main definitions

* `loadB`, `storeB`: an instruction has the shape of a load, of a store.

## Main results

* `loadB_of_renArr`, `loadB_of_renRM`, `storeB_of_renArr`, `storeB_of_renRM`: the renamings
  keep the shapes.
* `regionCoCode_loadStore`: a load of the code with its result copies directly followed by a
  store is a load and a store of the result copy, when the exported code has no such pair.
* `regionCoParts_noSelfPair`, `fieldDom_noSelfPair`: the hypothesis `hNP` from the absence of a
  load directly followed by a store in the exported code and distinct renamed bases of the
  result copy.
* `fieldDom_noMName`: on the field domain without a site of the multiplication fusion, no name
  of the code behind the prefix begins with `m`. The names of the code with its result copies
  and their coalesced images are names of the code (`codeName_regionCoCode`,
  `canon_codeName`), the pairs send a name to an allocated name or to itself
  (`allocName_head`), the merge pairs are empty and `selfNopI` adds no name.
* `fieldDom_foldPos_addSub_of_noLoadStore`, `fieldDom_foldPos_addSub_of_posShape`: the fold
  positions of the sum and the difference.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr renLoad renStore)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renLinstrR
  renOperand)

/-! ## 1. The shapes of a load and a store -/

/-- **The instruction has the shape of a load**: `LOADIDX` of one indexed operand into one
    register at a load tag. -/
def loadB : LinstrRM → Bool
  | (.Lopn [.reg _] o [.arrIdx _ _ _], .load _ _) => o == "LOADIDX"
  | _ => false

/-- **The instruction has the shape of a store**: `STOREIDX` of a register at one indexed
    operand into one register at a store tag. -/
def storeB : LinstrRM → Bool
  | (.Lopn [.reg _] o [.arrIdx _ _ _, .reg _], .store _ _) => o == "STOREIDX"
  | _ => false

/-- A pair of an array self-move is a load followed by a store. -/
theorem loadB_storeB_of_selfMoveB {i j : LinstrRM} (h : selfMoveB i j = true) :
    loadB i = true ∧ storeB j = true := by
  obtain ⟨t, a, z, s, w, n, rfl, rfl⟩ := selfMoveB_shape h
  exact ⟨rfl, rfl⟩

/-- The shape of a load. -/
theorem loadB_iff {i : LinstrRM} : loadB i = true ↔
    ∃ d b x s w n, i = (.Lopn [.reg d] "LOADIDX" [.arrIdx b x s], .load w n) := by
  constructor
  · intro h
    unfold loadB at h
    split at h
    · simp only [beq_iff_eq] at h
      subst h
      exact ⟨_, _, _, _, _, _, rfl⟩
    · cases h
  · rintro ⟨d, b, x, s, w, n, rfl⟩
    rfl

/-- The shape of a store. -/
theorem storeB_iff {i : LinstrRM} : storeB i = true ↔
    ∃ d b x s v w n, i = (.Lopn [.reg d] "STOREIDX" [.arrIdx b x s, .reg v], .store w n) := by
  constructor
  · intro h
    unfold storeB at h
    split at h
    · simp only [beq_iff_eq] at h
      subst h
      exact ⟨_, _, _, _, _, _, _, rfl⟩
    · cases h
  · rintro ⟨d, b, x, s, v, w, n, rfl⟩
    rfl

/-- An instruction whose renamed names have the shape of a load has the shape of a load. -/
theorem loadB_of_renRM {f : String → String} {i : LinstrRM} (h : loadB (renRM f i) = true) :
    loadB i = true := by
  obtain ⟨d, b, x, s, w, n, he⟩ := loadB_iff.mp h
  rcases i with ⟨wire, tag⟩
  simp only [renRM, Prod.mk.injEq] at he
  obtain ⟨hw, rfl⟩ := he
  cases wire with
  | Lopn ds o ss =>
      simp only [renLinstrR, LinstrR.Lopn.injEq, List.map_eq_singleton_iff] at hw
      obtain ⟨⟨d0, rfl, hd0⟩, rfl, ⟨s0, rfl, hs0⟩⟩ := hw
      obtain ⟨d1, rfl⟩ := JasminLsemExportShippedAnd.renOperand_eq_reg hd0
      obtain ⟨b1, x1, rfl, -, -⟩ :=
        (JasminLsemExportRewrites.renOperand_eq_arrIdx _ _ _ _ _).mp hs0
      rfl
  | _ => simp [renLinstrR] at hw

/-- An instruction whose renamed names have the shape of a store has the shape of a store. -/
theorem storeB_of_renRM {f : String → String} {i : LinstrRM} (h : storeB (renRM f i) = true) :
    storeB i = true := by
  obtain ⟨d, b, x, s, v, w, n, he⟩ := storeB_iff.mp h
  rcases i with ⟨wire, tag⟩
  simp only [renRM, Prod.mk.injEq] at he
  obtain ⟨hw, rfl⟩ := he
  cases wire with
  | Lopn ds o ss =>
      simp only [renLinstrR, LinstrR.Lopn.injEq, List.map_eq_singleton_iff] at hw
      obtain ⟨⟨d0, rfl, hd0⟩, rfl, hss⟩ := hw
      obtain ⟨d1, rfl⟩ := JasminLsemExportShippedAnd.renOperand_eq_reg hd0
      rcases ss with _ | ⟨s0, _ | ⟨s1, _ | ⟨_, _⟩⟩⟩ <;>
        simp only [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq, and_false,
          and_true, List.nil_eq] at hss
      obtain ⟨hs0, hs1⟩ := hss
      obtain ⟨b1, x1, rfl, -, -⟩ :=
        (JasminLsemExportRewrites.renOperand_eq_arrIdx _ _ _ _ _).mp hs0
      obtain ⟨v1, rfl⟩ := JasminLsemExportShippedAnd.renOperand_eq_reg hs1
      rfl
  | _ => simp [renLinstrR] at hw

/-- An instruction whose array positions renamed have the shape of a load has the shape of a
    load. -/
theorem loadB_of_renArr {f : String → String} {i : LinstrRM} (h : loadB (renArr f i) = true) :
    loadB i = true := by
  obtain ⟨d, b, x, s, w, n, he⟩ := loadB_iff.mp h
  rcases i with ⟨wire, tag⟩
  cases tag <;> simp only [renArr, Prod.mk.injEq, reduceCtorEq, and_false] at he
  obtain ⟨hw, -⟩ := he
  unfold renLoad at hw
  split at hw
  · split at hw
    · simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
        LOperand.arrIdx.injEq, and_true] at hw
      obtain ⟨rfl, rfl, -⟩ := hw
      rfl
    · simp only [LinstrR.Lopn.injEq] at hw
      exact absurd hw.2.1 ‹_›
  · subst hw
    rfl

/-- An instruction whose array positions renamed have the shape of a store has the shape of a
    store. -/
theorem storeB_of_renArr {f : String → String} {i : LinstrRM} (h : storeB (renArr f i) = true) :
    storeB i = true := by
  obtain ⟨d, b, x, s, v, w, n, he⟩ := storeB_iff.mp h
  rcases i with ⟨wire, tag⟩
  cases tag <;> simp only [renArr, Prod.mk.injEq, reduceCtorEq, and_false] at he
  obtain ⟨hw, -⟩ := he
  unfold renStore at hw
  split at hw
  · split at hw
    · simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
        LOperand.arrIdx.injEq, and_true] at hw
      obtain ⟨-, rfl, -⟩ := hw
      rfl
    · simp only [LinstrR.Lopn.injEq] at hw
      exact absurd hw.2.1 ‹_›
  · subst hw
    rfl

/-! ## 2. Loads followed by stores in the code with its result copies -/

/-- **A pair of consecutive positions of an appended code** lies in the first part, across the
    seam, or in the second part. -/
theorem pair_append {A B : List LinstrRM} {k : Nat} {i j : LinstrRM}
    (hi : (A ++ B)[k]? = some i) (hj : (A ++ B)[k + 1]? = some j) :
    (A[k]? = some i ∧ A[k + 1]? = some j) ∨ (A[k]? = some i ∧ B[0]? = some j)
      ∨ (A.length ≤ k ∧ B[k - A.length]? = some i ∧ B[k - A.length + 1]? = some j) := by
  by_cases h1 : k + 1 < A.length
  · rw [List.getElem?_append_left (by omega)] at hi
    rw [List.getElem?_append_left h1] at hj
    exact .inl ⟨hi, hj⟩
  · by_cases h2 : k < A.length
    · rw [List.getElem?_append_left h2] at hi
      rw [List.getElem?_append_right (by omega), show k + 1 - A.length = 0 by omega] at hj
      exact .inr (.inl ⟨hi, hj⟩)
    · rw [List.getElem?_append_right (by omega)] at hi
      rw [List.getElem?_append_right (by omega), show k + 1 - A.length = k - A.length + 1 by
        omega] at hj
      exact .inr (.inr ⟨by omega, hi, hj⟩)

/-- The copies of the pairs have no load. -/
theorem loadB_movesOf {ps : List (String × String)} {i : LinstrRM} (hi : i ∈ movesOf ps) :
    loadB i = false := by
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  rfl

/-- The copies of the pairs have no store. -/
theorem storeB_movesOf {ps : List (String × String)} {i : LinstrRM} (hi : i ∈ movesOf ps) :
    storeB i = false := by
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  rfl

/-- **A load of the result copy directly followed by a store** is the load of the word `jj` of
    the source followed by the store of the version `jj + 1` of the result buffer. -/
theorem resCopyCode_loadStore {src D : String} {m p : Nat} {i j : LinstrRM}
    (hi : (resCopyCode src D m)[p]? = some i) (hj : (resCopyCode src D m)[p + 1]? = some j)
    (hl : loadB i = true) :
    ∃ jj, jj < m ∧ i = (.Lopn [.reg copyTmp] "LOADIDX" [.arrIdx src copyIdx 8], .load 64 m)
      ∧ j = (.Lopn [.reg (copyName D (jj + 1))] "STOREIDX"
        [.arrIdx (copyName D jj) copyIdx 8, .reg copyTmp], .store 64 m) := by
  have hlt : p + 1 < 3 * m := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    rwa [length_resCopyCode] at this
  obtain ⟨jj, hjj, ⟨hp, h⟩ | ⟨hp, h⟩ | ⟨hp, h⟩⟩ :=
    resCopyCode_at (src := src) (D := D) (m := m) (p := p) (by omega)
  · rw [hi] at h
    cases h
    cases hl
  · rw [hi] at h
    cases h
    obtain ⟨jj', -, ⟨hp', h'⟩ | ⟨hp', h'⟩ | ⟨hp', h'⟩⟩ :=
      resCopyCode_at (src := src) (D := D) (m := m) (p := p + 1) hlt
    · omega
    · omega
    · rw [hj] at h'
      cases h'
      have he : jj' = jj := by omega
      subst he
      exact ⟨jj', hjj, rfl, rfl⟩
  · rw [hi] at h
    cases h
    cases hl

/-- The result copy begins with no store. -/
theorem storeB_resCopyCode_zero {src D : String} {m : Nat} {j : LinstrRM}
    (hj : (resCopyCode src D m)[0]? = some j) : storeB j = false := by
  have hlt : 0 < 3 * m := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    rwa [length_resCopyCode] at this
  obtain ⟨jj, -, ⟨-, h⟩ | ⟨hp, -⟩ | ⟨hp, -⟩⟩ :=
    resCopyCode_at (src := src) (D := D) (m := m) (p := 0) hlt
  · rw [hj] at h
    cases h
    rfl
  · omega
  · omega

/-- **A load of the code with its result copies directly followed by a store** is a load and a
    store of the result copy, when no load of the exported code is directly followed by a
    store. -/
theorem regionCoCode_loadStore (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    {code : List LinstrRM} (res : List LOperand) (cp : Option (String × String × Nat))
    (hC : ∀ (k : Nat) (i j : LinstrRM), code[k]? = some i → code[k + 1]? = some j →
      loadB i = true → storeB j = false)
    {k : Nat} {i j : LinstrRM} (hi : (regionCoCode σ nm t code res cp)[k]? = some i)
    (hj : (regionCoCode σ nm t code res cp)[k + 1]? = some j) (hl : loadB i = true)
    (hs : storeB j = true) :
    ∃ src D m jj, cp = some (src, D, m) ∧ jj < m
      ∧ i = (.Lopn [.reg copyTmp] "LOADIDX" [.arrIdx src copyIdx 8], .load 64 m)
      ∧ j = (.Lopn [.reg (copyName D (jj + 1))] "STOREIDX"
        [.arrIdx (copyName D jj) copyIdx 8, .reg copyTmp], .store 64 m) := by
  have hcm : ∀ {k : Nat} {i j : LinstrRM},
      (code ++ movesOf (regionRet σ nm t res).toList)[k]? = some i →
      (code ++ movesOf (regionRet σ nm t res).toList)[k + 1]? = some j →
      loadB i = true → storeB j = false := by
    intro k i j hi hj hl
    rcases pair_append hi hj with ⟨hi, hj⟩ | ⟨-, hj⟩ | ⟨-, hi, -⟩
    · exact hC k i j hi hj hl
    · exact storeB_movesOf (List.mem_of_getElem? hj)
    · rw [loadB_movesOf (List.mem_of_getElem? hi)] at hl
      cases hl
  unfold regionCoCode at hi hj
  split at hi
  · rw [hcm hi hj hl] at hs
    cases hs
  · rename_i src D m
    rcases pair_append hi hj with ⟨hi, hj⟩ | ⟨-, hj⟩ | ⟨-, hi, hj⟩
    · rw [hcm hi hj hl] at hs
      cases hs
    · rw [storeB_resCopyCode_zero hj] at hs
      cases hs
    · obtain ⟨jj, hjj, rfl, rfl⟩ := resCopyCode_loadStore hi hj hl
      exact ⟨src, D, m, jj, rfl, hjj, rfl, rfl⟩

/-! ## 3. The parts have no array self-move -/

/-- **The parts of the reference have no pair of an array self-move** behind the prefix, at
    every liveness table, when no load of the exported code is directly followed by a store and,
    at an array result copy `(src, D, m)`, the coalesced and renamed source is no coalesced and
    renamed version `copyName D jj`, `jj < m`, of the result buffer. -/
theorem regionCoParts_noSelfPair (σ : AbiLayout) (nm : String → String) (body : Lcmd)
    (t : JasminTy) {code : List LinstrRM} (res : List LOperand) (cert : List (String × String))
    (hC : ∀ (k : Nat) (i j : LinstrRM), code[k]? = some i → code[k + 1]? = some j →
      loadB i = true → storeB j = false)
    (hR : ∀ src D m, regionCopy σ nm t none code res = some (src, D, m) → ∀ jj, jj < m →
      renOf (regionCoParts σ nm body t code res cert).tau
          (renOf (regionCoParts σ nm body t code res cert).ps
            (regionAliasN σ nm t res
              (regionCoCode σ nm t code res (regionCopy σ nm t none code res)) src))
        ≠ renOf (regionCoParts σ nm body t code res cert).tau
          (renOf (regionCoParts σ nm body t code res cert).ps
            (regionAliasN σ nm t res
              (regionCoCode σ nm t code res (regionCopy σ nm t none code res))
              (copyName D jj))))
    (Lr : Nat → List String) (k : Nat) :
    selfPairB (regionCoParts σ nm body t code res cert).pre.length Lr
      ((regionCoParts σ nm body t code res cert).pre
        ++ (regionCoParts σ nm body t code res cert).merged) k = false := by
  set d := regionCoParts σ nm body t code res cert with hd
  set ρ := regionAliasN σ nm t res
    (regionCoCode σ nm t code res (regionCopy σ nm t none code res)) with hρ
  have hm : d.merged = (regionCoCode σ nm t code res (regionCopy σ nm t none code res)).map
      (fun c => renRM (renOf d.tau) (renRM (renOf d.ps) (renArr ρ c))) := by
    simp only [hd, regionCoParts, regionCoBody, List.map_map]
    rfl
  refine selfPairB_eq_false_of_selfMoveB (fun k i j hk hi hj => ?_) Lr k
  rw [List.getElem?_append_right hk, hm, List.getElem?_map] at hi
  rw [List.getElem?_append_right (by omega),
    show k + 1 - d.pre.length = k - d.pre.length + 1 by omega, hm, List.getElem?_map] at hj
  obtain ⟨i0, hi0, rfl⟩ := Option.map_eq_some_iff.mp hi
  obtain ⟨j0, hj0, rfl⟩ := Option.map_eq_some_iff.mp hj
  cases hsm : selfMoveB (renRM (renOf d.tau) (renRM (renOf d.ps) (renArr ρ i0)))
      (renRM (renOf d.tau) (renRM (renOf d.ps) (renArr ρ j0)))
  · rfl
  · exfalso
    obtain ⟨hl, hs⟩ := loadB_storeB_of_selfMoveB hsm
    obtain ⟨src, D, m, jj, hcp, hjj, rfl, rfl⟩ :=
      regionCoCode_loadStore σ nm t res _ hC hi0 hj0
      (loadB_of_renArr (loadB_of_renRM (loadB_of_renRM hl)))
      (storeB_of_renArr (storeB_of_renRM (storeB_of_renRM hs)))
    have hne := hR src D m hcp jj hjj
    simp only [selfMoveB, renArr, renLoad, renStore, renRM, renLinstrR, renOperand, ite_true,
      List.map_cons, List.map_nil, Bool.and_eq_true, beq_iff_eq] at hsm
    exact hne hsm.1.1.1.1.1.2

/-! ## 4. The field domain -/

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **The hypothesis `hNP` of `fieldDom_foldPos_of_loadsChainK` on the field domain**, when no
    load of the exported code is directly followed by a store and, at an array result copy
    `(src, D, m)`, the coalesced source renamed by the pairs is no coalesced version
    `copyName D jj`, `jj < m`, of the result buffer renamed by the pairs. The merge pairs of
    the field domain are empty (`fieldDom_tau_nil`). -/
theorem fieldDom_noSelfPair (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert)
    (hC : ∀ (k : Nat) (i j : LinstrRM), r.code[k]? = some i → r.code[k + 1]? = some j →
      loadB i = true → storeB j = false)
    (hR : ∀ src D m, regionCopy σ exportReg t none r.code r.res = some (src, D, m) →
      ∀ jj, jj < m →
      renOf (regionCoParts σ exportReg b t r.code r.res cert).ps
          (regionAliasN σ exportReg t r.res (regionCoCode σ exportReg t r.code r.res
            (regionCopy σ exportReg t none r.code r.res)) src)
        ≠ renOf (regionCoParts σ exportReg b t r.code r.res cert).ps
          (regionAliasN σ exportReg t r.res (regionCoCode σ exportReg t r.code r.res
            (regionCopy σ exportReg t none r.code r.res)) (copyName D jj))) :
    ∀ k, selfPairB (regionCoParts σ exportReg b t r.code r.res cert).pre.length
      (liveAt (tabAt (regionCoParts σ exportReg b t r.code r.res cert).liveM)
        ((regionCoParts σ exportReg b t r.code r.res cert).pre
          ++ (regionCoParts σ exportReg b t r.code r.res cert).merged).length)
      ((regionCoParts σ exportReg b t r.code r.res cert).pre
        ++ (regionCoParts σ exportReg b t r.code r.res cert).merged) k = false := by
  have hτ := fieldDom_tau_nil h hB
  refine regionCoParts_noSelfPair σ exportReg b t r.res cert hC (fun src D m hcp jj hjj => ?_) _
  rw [hτ]
  exact hR src D m hcp jj hjj

/-- **The fold positions of the sum and the difference of the field domain** from the shape
    `LoadsChainK`, the conditions of `fieldDom_noSelfPair` and the fold class. -/
theorem fieldDom_foldPos_addSub_of_noLoadStore (h : fieldDomB'' e σ = true)
    (hA : FieldAddSub e) (hB : FieldBody e σ fname b t r cert)
    (hL : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → LoadsChainK (fun _ => none) (legalizeRegion q'))
    (hC : ∀ (k : Nat) (i j : LinstrRM), r.code[k]? = some i → r.code[k + 1]? = some j →
      loadB i = true → storeB j = false)
    (hR : ∀ src D m, regionCopy σ exportReg t none r.code r.res = some (src, D, m) →
      ∀ jj, jj < m →
      renOf (regionCoParts σ exportReg b t r.code r.res cert).ps
          (regionAliasN σ exportReg t r.res (regionCoCode σ exportReg t r.code r.res
            (regionCopy σ exportReg t none r.code r.res)) src)
        ≠ renOf (regionCoParts σ exportReg b t r.code r.res cert).ps
          (regionAliasN σ exportReg t r.res (regionCoCode σ exportReg t r.code r.res
            (regionCopy σ exportReg t none r.code r.res)) (copyName D jj)))
    (hP : ∀ (k : Nat) (i : LinstrRM),
      ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      PosClass (regionCoParts σ exportReg b t r.code r.res cert).cells i) :
    ∀ k i, ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      FoldPos (regionCoParts σ exportReg b t r.code r.res cert).cells
        ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
          (regionCoParts σ exportReg b t r.code r.res cert).pre.length) k i :=
  fieldDom_foldPos_addSub_of_loadsChainK h hA hB hL
    (fieldDom_noSelfPair (fieldDomB_of_fieldDomB'' h) hB hC hR) hP

/-! ## 5. Names that begin with no `m` -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseMulHiRM)

/-- A name of a renamed wire is the image of a name of the wire. -/
theorem mem_instrNames_renLinstrR {f : String → String} {w : LinstrR} {x : String}
    (h : x ∈ instrNames (renLinstrR f w)) : ∃ y ∈ instrNames w, x = f y := by
  have ho : ∀ o : LOperand, opNames (renOperand f o) = (opNames o).map f := by
    intro o
    cases o <;> rfl
  cases w with
  | Lopn ds o ss =>
      simp only [renLinstrR, instrNames, ← List.map_append, List.flatMap_map, ho,
        List.mem_flatMap, List.mem_map] at h
      obtain ⟨op, hop, y, hy, rfl⟩ := h
      exact ⟨y, List.mem_flatMap.mpr ⟨op, hop, hy⟩, rfl⟩
  | _ => simp [renLinstrR, instrNames] at h

/-- A name of the replacement `selfNopI` of an instruction is a name of the instruction. -/
theorem mem_instrNames_selfNopI {i : LinstrRM} {x : String}
    (h : x ∈ instrNames (selfNopI i).1) : x ∈ instrNames i.1 := by
  unfold selfNopI at h
  split at h
  · rename_i ds o b z s rest he
    rw [he]
    simp only [instrNames, opNames, List.cons_append, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] at h
    have hx : x = z := by simpa using h
    subst hx
    simp only [instrNames, List.mem_flatMap, List.mem_append, List.mem_cons]
    exact ⟨.arrIdx b x s, .inr (.inl rfl), by simp [opNames]⟩
  · exact h

/-- An instruction of `selfNop` is the instruction at its position or its replacement. -/
theorem getElem?_selfNop {k0 : Nat} {Lr : Nat → List String} {B : List LinstrRM} {k : Nat}
    {i : LinstrRM} (h : (selfNop k0 Lr B)[k]? = some i) :
    ∃ i0, B[k]? = some i0 ∧ (i = i0 ∨ i = selfNopI i0) := by
  simp only [selfNop, List.getElem?_mapIdx, Option.map_eq_some_iff] at h
  obtain ⟨i0, hi0, he⟩ := h
  refine ⟨i0, hi0, ?_⟩
  split at he
  · exact .inr he.symm
  · exact .inl he.symm

/-- A name of the code does not begin with `m`. -/
theorem CodeName.head_ne_m {x : String} (h : CodeName x) : x.toList.head? ≠ some 'm' := by
  rcases (codeName_iff x).mp h with h | h | h <;> rw [h] <;> decide

/-- **No name of the code behind the prefix of the parts begins with `m`** on the field domain,
    when the code has no site of the multiplication fusion. -/
theorem fieldDom_noMName (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert)
    (hs : (regionCoParts σ exportReg b t r.code r.res cert).sites = false) :
    ∀ (k : Nat) (i : LinstrRM),
      ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      NoMName i := by
  have hτ := fieldDom_tau_nil h hB
  obtain ⟨B, tbl, hc, hcert⟩ := cert_allocCertOf h hB
  subst hcert
  have hret : ∀ res, regionRet σ exportReg t res = none := by
    obtain ⟨-, R, n, hR⟩ := fieldDomB_abi h
    exact fun _ => regionRet_words hR
  obtain ⟨k0, n, hk0, ha, hres⟩ := fieldDomB_layout h
  have hbuf := fieldDom_regionResBuf hk0 ha hres
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, hr, -, -, rfl⟩ := hB
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal h) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hcf : (legalizeRegion q').callFree = true :=
    legalizeRegion_callFree ((NarrowWords.callFree_narrowPrep hq').trans (fieldDom_callFree h hq))
  have hEx : regionExportableB (legalizeRegion q') = true := fieldDom_legalize hE1
  have hX : RegionExp fname (legalizeRegion q') (regionWebsEx σ exportReg) r := by
    rw [hr]
    exact regionExp_webs _ hr0
  have hsym : ∀ i ∈ r.code, RegionExportDefInit.symReads i = [] := fun i hi =>
    (hX.mnemDom hEx hcf i hi).1
  have hlen : ((nfCtx σ).map NarrowWords.wideTy).length ≤ σ.args.length := by
    rw [List.length_map]
    exact (RegionAllocMapDom.nfCtx_length σ).le
  have hL := codeName_regionCoCode fname _ hEx hcf hX σ exportReg (NarrowWords.wideTy t0) hsym
    hlen (hret _)
  have hnsC := RegionCoComplete.noShadow_regionCoCode σ exportReg (NarrowWords.wideTy t0)
    r.code r.res (regionCopy σ exportReg (NarrowWords.wideTy t0) none r.code r.res)
    (hX.noShadow hEx hcf)
  have hρ := canon_codeName (t := NarrowWords.wideTy t0) (res := r.res) hL hnsC
    (fun D n' hb => by
      rw [hbuf] at hb
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hb)
      exact codeName_argName 0)
  intro k i hk
  set d := regionCoParts σ exportReg b (NarrowWords.wideTy t0) r.code r.res
    (allocCertOf B tbl) with hd
  set ρ := regionAliasN σ exportReg (NarrowWords.wideTy t0) r.res
    (regionCoCode σ exportReg (NarrowWords.wideTy t0) r.code r.res
      (regionCopy σ exportReg (NarrowWords.wideTy t0) none r.code r.res)) with hρd
  have hm : d.merged = (regionCoCode σ exportReg (NarrowWords.wideTy t0) r.code r.res
      (regionCopy σ exportReg (NarrowWords.wideTy t0) none r.code r.res)).map
      (fun c => renRM (renOf d.tau) (renRM (renOf d.ps) (renArr ρ c))) := by
    simp only [hd, regionCoParts, regionCoBody, List.map_map]
    rfl
  have hfu : d.fused = if d.sites then d.pre ++ fuseMulHiRM (d.nop.drop d.pre.length)
      else d.nop := rfl
  have hn : d.nop = selfNop d.pre.length (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length)
      (d.pre ++ d.merged) := rfl
  rw [hfu, hs, ite_eq_right Bool.false_ne_true, List.getElem?_drop, hn] at hk
  obtain ⟨i0, hi0, hii⟩ := getElem?_selfNop hk
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, hm,
    List.getElem?_map] at hi0
  obtain ⟨c, hc0, rfl⟩ := Option.map_eq_some_iff.mp hi0
  have hcm := List.mem_of_getElem? hc0
  intro x hx
  replace hx : x ∈ instrNames (renRM (renOf d.tau) (renRM (renOf d.ps) (renArr ρ c))).1 := by
    rcases hii with rfl | rfl
    · exact hx
    · exact mem_instrNames_selfNopI hx
  obtain ⟨y1, hy1, rfl⟩ := mem_instrNames_renLinstrR hx
  obtain ⟨y2, hy2, rfl⟩ := mem_instrNames_renLinstrR hy1
  have hy2c : CodeName y2 := by
    rcases under_renArr _ (hnsC c hcm) _ hy2 with h' | ⟨y, hy, he⟩
    · exact hL c hcm _ h'
    · rw [he]
      exact hρ y (hL c hcm y hy)
  rw [hτ]
  change (renOf (certArgs σ (allocCertOf B tbl)) y2).toList.head? ≠ some 'm'
  unfold certArgs
  rw [RegionAllocMapComplete.renOf_filter_allocCertOf]
  split_ifs
  · exact allocName_head hc _
  · exact hy2c.head_ne_m

/-- **The fold positions of the sum and the difference of the field domain** from the shape
    `LoadsChainK`, the conditions of `fieldDom_noSelfPair` and the shape `PosShape` of the
    fold class at every position of the code behind the prefix: no name of that code begins
    with `m` (`fieldDom_noMName`). -/
theorem fieldDom_foldPos_addSub_of_posShape (h : fieldDomB'' e σ = true)
    (hA : FieldAddSub e) (hB : FieldBody e σ fname b t r cert)
    (hL : ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]),
      haxEntry.chainNF (Hax.HaxModule.single e) σ = some ⟨t0, q⟩ →
      NarrowWords.narrowPrep q = some q' → LoadsChainK (fun _ => none) (legalizeRegion q'))
    (hC : ∀ (k : Nat) (i j : LinstrRM), r.code[k]? = some i → r.code[k + 1]? = some j →
      loadB i = true → storeB j = false)
    (hR : ∀ src D m, regionCopy σ exportReg t none r.code r.res = some (src, D, m) →
      ∀ jj, jj < m →
      renOf (regionCoParts σ exportReg b t r.code r.res cert).ps
          (regionAliasN σ exportReg t r.res (regionCoCode σ exportReg t r.code r.res
            (regionCopy σ exportReg t none r.code r.res)) src)
        ≠ renOf (regionCoParts σ exportReg b t r.code r.res cert).ps
          (regionAliasN σ exportReg t r.res (regionCoCode σ exportReg t r.code r.res
            (regionCopy σ exportReg t none r.code r.res)) (copyName D jj)))
    (hS : ∀ (k : Nat) (i : LinstrRM),
      ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      PosShape (regionCoParts σ exportReg b t r.code r.res cert).cells i) :
    ∀ k i, ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      FoldPos (regionCoParts σ exportReg b t r.code r.res cert).cells
        ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
          (regionCoParts σ exportReg b t r.code r.res cert).pre.length) k i :=
  fieldDom_foldPos_addSub_of_noLoadStore h hA hB hL hC hR
    (posClass_parts_of_posShape _
      (fieldDom_noMName (fieldDomB_of_fieldDomB'' h) hB
        (fieldDom_sites_addSub (fieldDomB_of_fieldDomB'' h) hA hB)) hS)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
