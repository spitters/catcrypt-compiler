/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCT

/-!
# The owned `Lprog` stages preserve direct addressing

`AllocCTPreservation.lcmdDirect` is the class of bodies with no register-indexed
operand: every memory access is at a base register and a compile-time
displacement, so the address trace of the gathered block does not depend on any
register, flag or memory value (`ConstantTimeCoverage.allDirect_constant_time`).
This module shows that each stage of `LprogOptPipeline.ownedLprog` maps the class
into itself, and composes the result with `toLprogPhysAbi_lcmdDirect`.

* `optimizeBasicBlocks_lcmdDirect`: the basic-block optimizer. Reload elimination,
  spill-pair elimination and dead-copy elimination delete instructions; scheduling
  permutes them; copy propagation replaces a register source by the source of a
  recorded move, which is a register or an immediate (`isFactSrc`); load CSE
  replaces a reload by a register move.
* `foldIndexedBody_lcmdDirect`: the constant-index fold replaces an indexed access
  by a direct one, the dead-move elimination deletes instructions, and the
  spelling writes a direct access with a `mem.<B>.<off>` register-shaped name.
* `ownedLprog_lcmdDirect`: the three stages in sequence, the third being
  `LprogGpReallocCT.reallocLprog_lcmdDirect`.
* `ownedLprog_toLprogPhysAbi_constant_time`: for a `Com` whose virtual body is
  index-free, every function of the owned `Lprog` gathers (under
  `ConstIndexFold.gatherPrinted`) to a block whose address and branch trace is the
  same from any two machine states.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogDirect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
  (isIndexed linstrRDirect lcmdDirect lcmdDirect_iff toLprogPhysAbi_lcmdDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
open CatCrypt.Crypto.Optimizer.LoadCSE (loadCSE loadCSEAux loadCSE_eq stepLoad asWideReload)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold

/-! ## 1. Generic closure facts -/

theorem lcmdDirect_of_forall_mem {a b : Lcmd}
    (h : ∀ i ∈ a, i ∈ b ∨ linstrRDirect i.li_i = true) (hb : lcmdDirect b = true) :
    lcmdDirect a = true := by
  rw [lcmdDirect_iff] at hb ⊢
  intro i hi
  rcases h i hi with h | h
  · exact hb i h
  · exact h

theorem lcmdDirect_of_sublist {a b : Lcmd} (h : a.Sublist b) (hb : lcmdDirect b = true) :
    lcmdDirect a = true :=
  lcmdDirect_of_forall_mem (fun _ hi => Or.inl (h.subset hi)) hb

theorem lcmdDirect_of_perm {a b : Lcmd} (h : (a.map Linstr.li_i).Perm (b.map Linstr.li_i))
    (hb : lcmdDirect b = true) : lcmdDirect a = true := by
  rw [lcmdDirect_iff] at hb ⊢
  intro i hi
  have hm : i.li_i ∈ b.map Linstr.li_i := h.subset (List.mem_map_of_mem hi)
  obtain ⟨j, hj, he⟩ := List.mem_map.1 hm
  rw [← he]
  exact hb j hj

/-! ## 2. The basic-block optimizer -/

theorem rewriteOperand_not_indexed {facts : List MoveFact} {w : Nat} {allowImm : Bool}
    {dstSelf : Option String} (hf : ∀ f ∈ facts, isIndexed f.2.1 = false) {o : LOperand}
    (ho : isIndexed o = false) :
    isIndexed (rewriteOperand facts w allowImm dstSelf o) = false := by
  cases o with
  | reg u =>
      simp only [rewriteOperand]
      split
      · split
        · rename_i v fw hl
          obtain ⟨f, hfm, hfe⟩ := List.exists_of_findSome?_eq_some hl
          split at hfe
          · simp only [Option.some.injEq] at hfe
            split
            · have := hf f hfm
              rw [hfe] at this
              exact this
            · rfl
          · cases hfe
        · rfl
      · rfl
  | _ => exact ho

theorem moveShape_not_indexed {i : Linstr} {d : String} {src : LOperand} {w : Nat}
    (h : moveShape i = some (d, src, w)) : isIndexed src = false := by
  unfold moveShape at h
  split at h
  · rename_i src' _
    split at h
    · rename_i hc
      dsimp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, -⟩ := h
        simp only [Bool.and_eq_true] at hc
        have hs := hc.2
        cases src' <;> simp_all [isFactSrc, isIndexed]
      · cases h
    · cases h
  · cases h

theorem propagateAux_lcmdDirect :
    ∀ (body : Lcmd) (facts : List MoveFact), (∀ f ∈ facts, isIndexed f.2.1 = false) →
      lcmdDirect body = true → lcmdDirect (propagateAux facts body) = true := by
  intro body
  induction body with
  | nil => intro _ _ _; rfl
  | cons i rest ih =>
      intro facts hf hb
      simp only [lcmdDirect, List.all_cons, Bool.and_eq_true] at hb
      obtain ⟨hi, hrest⟩ := hb
      simp only [propagateAux]
      split
      · rename_i dsts opn srcs heq
        split
        · simp only [lcmdDirect, List.all_cons, Bool.and_eq_true]
          refine ⟨?_, ih _ ?_ hrest⟩
          · rw [heq] at hi
            simp only [linstrRDirect, Bool.and_eq_true, List.all_eq_true] at hi ⊢
            refine ⟨hi.1, fun o ho => ?_⟩
            obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
            have := hi.2 o' ho'
            simp only [Bool.not_eq_true'] at this ⊢
            exact rewriteOperand_not_indexed hf this
          · have hk : ∀ (fs : List MoveFact) (rs : List String),
                (∀ f ∈ fs, isIndexed f.2.1 = false) →
                ∀ f ∈ rs.foldl killFacts fs, isIndexed f.2.1 = false := by
              intro fs rs hfs
              induction rs generalizing fs with
              | nil => exact hfs
              | cons r rs ihr =>
                  exact ihr _ (fun f hf' => hfs f (List.mem_of_mem_filter hf'))
            have h1 := hk facts (regDefsOf dsts) hf
            split
            · rename_i d src w hms
              split
              · exact h1
              · intro f hf'
                rcases List.mem_cons.1 hf' with rfl | hf'
                · exact moveShape_not_indexed hms
                · exact h1 f hf'
            · exact h1
        · simp only [lcmdDirect, List.all_cons, Bool.and_eq_true]
          exact ⟨hi, ih _ (by simp) hrest⟩
      · simp only [lcmdDirect, List.all_cons, Bool.and_eq_true]
        exact ⟨hi, ih _ (by simp) hrest⟩

theorem copyPropagateBody_lcmdDirect {body : Lcmd} (h : lcmdDirect body = true) :
    lcmdDirect (copyPropagateBody body) = true :=
  lcmdDirect_of_sublist (deadElimBody_sublist _)
    (propagateAux_lcmdDirect body [] (by simp) h)

theorem stepLoad_mem (h : CatCrypt.Crypto.Optimizer.LoadCSE.LoadEnv) (i : Linstr) :
    (stepLoad h i).1 = i ∨ linstrRDirect (stepLoad h i).1.li_i = true := by
  unfold stepLoad
  split
  · split
    · split
      · exact Or.inl rfl
      · right
        simp [linstrRDirect, isIndexed]
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem loadCSEAux_lcmdDirect :
    ∀ (body : Lcmd) (h : CatCrypt.Crypto.Optimizer.LoadCSE.LoadEnv),
      lcmdDirect body = true → lcmdDirect (loadCSEAux h body) = true := by
  intro body
  induction body with
  | nil => intro _ _; rfl
  | cons i rest ih =>
      intro h hb
      simp only [lcmdDirect, List.all_cons, Bool.and_eq_true] at hb
      rw [CatCrypt.Crypto.Optimizer.LoadCSE.loadCSEAux_cons]
      simp only [lcmdDirect, List.all_cons, Bool.and_eq_true]
      refine ⟨?_, ih _ hb.2⟩
      rcases stepLoad_mem h i with he | he
      · rw [he]; exact hb.1
      · exact he

theorem loadCSE_lcmdDirect {body : Lcmd} (h : lcmdDirect body = true) :
    lcmdDirect (loadCSE body) = true := by
  rw [loadCSE_eq]
  exact loadCSEAux_lcmdDirect body [] h

theorem optRunBody_lcmdDirect {body : Lcmd} (h : lcmdDirect body = true) :
    lcmdDirect (optRunBody body) = true := by
  unfold optRunBody
  split
  · refine loadCSE_lcmdDirect (copyPropagateBody_lcmdDirect ?_)
    refine lcmdDirect_of_perm
      (CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler.scheduleBody_instr_multiset _) ?_
    refine lcmdDirect_of_sublist
      (CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim.reloadElimBody_sublist _) ?_
    exact lcmdDirect_of_sublist
      (CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad.elimReloads_sublist _) h
  · exact h

/-- **The basic-block optimizer preserves direct addressing.** -/
theorem optimizeBasicBlocks_lcmdDirect {body : Lcmd} (h : lcmdDirect body = true) :
    lcmdDirect (optimizeBasicBlocks body) = true := by
  have hseg : ∀ seg ∈ splitStraightRuns body, lcmdDirect seg = true := by
    intro seg hseg
    have hs : seg.Sublist body := by
      have := List.sublist_flatten_of_mem hseg
      rwa [splitStraightRuns_flatten] at this
    exact lcmdDirect_of_sublist hs h
  unfold optimizeBasicBlocks
  rw [lcmdDirect_iff]
  intro i hi
  obtain ⟨seg', hseg', hi'⟩ := List.mem_flatten.1 hi
  obtain ⟨seg, hsm, rfl⟩ := List.mem_map.1 hseg'
  have hd : lcmdDirect (if bodyIsStraightLine seg then optRunBody seg else seg) = true := by
    split
    · exact optRunBody_lcmdDirect (hseg seg hsm)
    · exact hseg seg hsm
  exact (lcmdDirect_iff _).1 hd i hi'

theorem optimizeLprogBasicBlocks_lcmdDirect {p : Lprog}
    (h : ∀ f ∈ p.lp_funcs, lcmdDirect f.2.lfd_body = true) :
    ∀ f ∈ (optimizeLprogBasicBlocks p).lp_funcs, lcmdDirect f.2.lfd_body = true := by
  intro f hf
  simp only [optimizeLprogBasicBlocks, mapBodies, List.mem_map] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  exact optimizeBasicBlocks_lcmdDirect (h g hg)

/-! ## 3. The constant-index fold stage -/

theorem foldCore_lcmdDirect_of (p : Nat × Nat × Nat) :
    ∀ (body : Lcmd) (env : KEnv), lcmdDirect body = true →
      lcmdDirect (foldCore p env body) = true := by
  intro body
  induction body with
  | nil => intro _ _; rfl
  | cons i rest ih =>
      intro env hb
      simp only [lcmdDirect, List.all_cons, Bool.and_eq_true] at hb
      simp only [foldCore, lcmdDirect, List.all_cons, Bool.and_eq_true]
      refine ⟨?_, ih _ hb.2⟩
      unfold foldInstr
      cases hf : foldTarget? env i.li_i with
      | none => exact hb.1
      | some i' => exact foldTarget?_direct hf

theorem constIndexFoldBody_lcmdDirect_of {body : Lcmd} (h : lcmdDirect body = true) :
    lcmdDirect (constIndexFoldBody body) = true := by
  unfold constIndexFoldBody
  dsimp only
  split
  · exact foldCore_lcmdDirect_of _ body [] h
  · exact h

theorem dropDeadCore_sublist (p : Nat × Nat × Nat) :
    ∀ (body : Lcmd), (dropDeadCore p body).Sublist body := by
  intro body
  induction body with
  | nil => exact List.Sublist.slnil
  | cons i rest ih =>
      simp only [dropDeadCore]
      split
      · split
        · exact ih.cons i
        · exact ih.cons_cons i
      · exact ih.cons_cons i

theorem dropDeadImmBody_sublist (body : Lcmd) : (dropDeadImmBody body).Sublist body := by
  unfold dropDeadImmBody
  dsimp only
  split
  · exact dropDeadCore_sublist _ body
  · exact List.Sublist.refl _

theorem spellMemInstr_mem (i : LinstrR) :
    spellMemInstr i = i ∨ linstrRDirect (spellMemInstr i) = true := by
  unfold spellMemInstr
  split
  · right; split <;> simp [linstrRDirect, isIndexed]
  · right; split <;> simp [linstrRDirect, isIndexed]
  · exact Or.inl rfl

theorem spellMemBody_lcmdDirect {body : Lcmd} (h : lcmdDirect body = true) :
    lcmdDirect (spellMemBody body) = true := by
  rw [lcmdDirect_iff] at h ⊢
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  rcases spellMemInstr_mem j.li_i with he | he
  · simp only [he]; exact h j hj
  · exact he

/-- **The fold stage preserves direct addressing.** -/
theorem foldIndexedBody_lcmdDirect {body : Lcmd} (h : lcmdDirect body = true) :
    lcmdDirect (foldIndexedBody body) = true :=
  spellMemBody_lcmdDirect (lcmdDirect_of_sublist (dropDeadImmBody_sublist _)
    (constIndexFoldBody_lcmdDirect_of h))

theorem foldIndexedLprog_lcmdDirect {p : Lprog}
    (h : ∀ f ∈ p.lp_funcs, lcmdDirect f.2.lfd_body = true) :
    ∀ f ∈ (foldIndexedLprog p).lp_funcs, lcmdDirect f.2.lfd_body = true := by
  intro f hf
  simp only [foldIndexedLprog, List.mem_map] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  exact foldIndexedBody_lcmdDirect (h g hg)

/-! ## 4. The owned back end -/

/-- **The owned back end preserves direct addressing.** -/
theorem ownedLprog_lcmdDirect {p : Lprog}
    (h : ∀ f ∈ p.lp_funcs, lcmdDirect f.2.lfd_body = true) :
    ∀ f ∈ (ownedLprog p).lp_funcs, lcmdDirect f.2.lfd_body = true :=
  LprogGpReallocCT.reallocLprog_lcmdDirect
    (foldIndexedLprog_lcmdDirect (optimizeLprogBasicBlocks_lcmdDirect h))

/-- **Constant time of the owned `Lprog` of an index-free `Com`.** If the virtual
    body of `com` has no register-indexed operand, every function of
    `ownedLprog (Com.toLprogPhysAbi com …)` that gathers under `gatherPrinted`
    gathers to a block whose address and branch trace is the same from any two
    machine states. -/
theorem ownedLprog_toLprogPhysAbi_constant_time {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap)
    (abiArgs : List String) (abiTyin : List Nat) (residence : Option (Array Nat))
    (abiW : Nat) (forceLivePin : Bool)
    (h : lcmdDirect (comToLfundef com immSlotMap).lfd_body = true)
    {f : String × Lfundef} {g : List (Jasmin.JInstr 64)}
    (hf : f ∈ (ownedLprog (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap
      outStoreMap abiArgs abiTyin residence abiW forceLivePin)).lp_funcs)
    (hg : gatherPrinted f.2.lfd_body = some g) (s₁ s₂ : Jasmin.JState 64) :
    MachineConstantTime.blockLeak s₁ g = MachineConstantTime.blockLeak s₂ g :=
  ConstantTimeCoverage.allDirect_constant_time g
    (gatherPrinted_allDirect
      (ownedLprog_lcmdDirect
        (toLprogPhysAbi_lcmdDirect com fname shiftImm immSlotMap inLoadMap outStoreMap
          abiArgs abiTyin residence abiW forceLivePin h) f hf) hg) s₁ s₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogDirect
