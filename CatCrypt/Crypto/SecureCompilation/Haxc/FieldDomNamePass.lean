/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomFold
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate

/-!
# The names of the printed body through the passes

A name is good (`GoodName`) when, as a cell name `memName A o`, its base `A` is the address
scratch register `R14`, and when it is no stack-argument name `RSP+off`. An instruction is
good (`NamesOK`) when every name it mentions is good. A body of good instructions has every
cell name at the base `R14` (`cellBaseScratch_of_namesOK`) and reads no stack-argument name
(`stackReadFreeB_of_namesOK`).

The passes from the allocated body to the printed body keep good instructions. Before the
constant-index fold the predicate also asks that the base of a register-indexed or a
displacement first source is `R14` (`FoldOK`): the fold spells the access `A[x]` at a known
index as the cell name `memName A off`. Every name a pass writes is a name of its input, a
general-purpose register, a reserved scratch register or its save slot, or a holder the pass
recorded from an earlier instruction:

* the high-product fusion writes the operands of the high product, `RDX`, the reserved
  scratches `R14` and `R15` and the recorded homes of low products;
* the copy propagation rewrites a source into a general-purpose register or an immediate, and
  the load CSE redirects a reload onto a register an earlier reload wrote;
* the fold writes `memName R14 off` from an access at the base `R14`;
* the re-allocation writes a name of its run or a register of the pool;
* the two-address legalisation writes `R15` and its save slot, the compare reload `R15`;
* the dead-write elimination and the frame trim keep a sublist.

## Main definitions

* `GoodName` — a name whose cell base is `R14` and that is no stack-argument name.
* `NamesOK` — every name of the instruction is good.
* `FoldOK` — `NamesOK`, with the indexed and displacement first sources at the base `R14`.

## Main results

* `cellBaseScratch_of_namesOK`, `stackReadFreeB_of_namesOK` — the two facts of a body of good
  instructions.
* `foldOK_fuseMulHiAux`, `foldOK_optimizeBasicBlocks`, `namesOK_foldIndexedBody`,
  `namesOK_reallocBody`, `namesOK_twoAddrBody`, `namesOK_cmpReload`, `namesOK_frameTrim` —
  the passes keep the predicates.
* `namesOK_printed` — every instruction of the trimmed printed body of an allocated body of
  `FoldOK` instructions is good.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (stackReadFreeB)

/-! ## 1. Good names -/

/-- **A good name**: as a cell name `memName A o` its base `A` is `R14`, and it is no
    stack-argument name `RSP+off`. -/
def GoodName (n : String) : Prop :=
  (∀ A o, n = memName A o → A = "R14") ∧ abiStackOff? n = none

/-- A name that does not begin with `R` is no stack-argument name. -/
theorem abiStackOff?_of_head {n : String} (h : n.toList.head? ≠ some 'R') :
    abiStackOff? n = none := by
  unfold abiStackOff?
  split
  · rename_i ds hds
    rw [hds] at h
    simp at h
  · rfl

/-- A name that does not begin with `m` and is no stack-argument name is good. -/
theorem goodName_of_head {n : String} (hm : n.toList.head? ≠ some 'm')
    (hR : abiStackOff? n = none) : GoodName n :=
  ⟨fun A o h => absurd (h ▸ memName_head A o) hm, hR⟩

/-- **A cell name at the base `R14` is good.** -/
theorem goodName_memName_R14 (o : Nat) : GoodName (memName "R14" o) :=
  ⟨fun _ _ h => (memName_inj h).1.symm,
    abiStackOff?_of_head (by rw [memName_head]; decide)⟩

/-- **A general-purpose register is good.** -/
theorem goodName_of_physGP {s : String} (h : X86Backend.LcmdCopyPropagate.isPhysGP s = true) :
    GoodName s := by
  have hm : s ∈ X86Backend.LcmdCopyPropagate.physGPs := by
    simpa [X86Backend.LcmdCopyPropagate.isPhysGP] using h
  simp only [X86Backend.LcmdCopyPropagate.physGPs, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    exact goodName_of_head (by decide) (by decide)

/-- **An allocated name is good**: the allocation pool, the vector registers and the spill
    names `k.*`, `kv.*` are no cell names and no stack-argument names. -/
theorem goodName_physRegName (p : Nat) : GoodName (physRegName p) := by
  refine goodName_of_head (physRegName_head p) ?_
  unfold physRegName
  split_ifs
  · dsimp only
    split
    · rename_i x hx
      have hm := List.mem_of_getElem? hx
      clear hx
      revert x
      decide
    · exact abiStackOff?_of_head (by simp [String.toList_append])
  · split
    · rename_i x hx
      have hm := List.mem_of_getElem? hx
      clear hx
      revert x
      decide
    · exact abiStackOff?_of_head (by simp [String.toList_append])

/-! ## 2. Good instructions -/

/-- **A good instruction**: every name it mentions is good. -/
def NamesOK (j : Linstr) : Prop := ∀ n ∈ instrNames j.li_i, GoodName n

/-- **A good instruction before the fold**: a good instruction whose indexed load or store,
    or displacement load or store, in the shapes the fold reads, has the base `R14`. -/
def FoldOK (j : Linstr) : Prop :=
  NamesOK j ∧
    (∀ d B x sc, j.li_i = .Lopn [.reg d] "LOADIDX" [.arrIdx B x sc] → B = "R14") ∧
    (∀ d B x sc vn, j.li_i = .Lopn [.reg d] "STOREIDX" [.arrIdx B x sc, .reg vn] →
      B = "R14") ∧
    (∀ d B off, j.li_i = .Lopn [.reg d] "LOAD" [.arr B off] → B = "R14") ∧
    (∀ d B off vn, j.li_i = .Lopn [.reg d] "STORE" [.arr B off, .reg vn] → B = "R14")

/-- The names of an operation. -/
theorem mem_instrNames_lopn {ds ss : List LOperand} {o n : String} :
    n ∈ instrNames (.Lopn ds o ss) ↔ (∃ a ∈ ds, n ∈ JasminLsemExportRewrites.opNames a) ∨ ∃ a ∈ ss, n ∈ JasminLsemExportRewrites.opNames a := by
  simp only [instrNames, List.mem_flatMap, List.mem_append]
  constructor
  · rintro ⟨a, ha | ha, hn⟩
    · exact Or.inl ⟨a, ha, hn⟩
    · exact Or.inr ⟨a, ha, hn⟩
  · rintro (⟨a, ha, hn⟩ | ⟨a, ha, hn⟩)
    · exact ⟨a, Or.inl ha, hn⟩
    · exact ⟨a, Or.inr ha, hn⟩

/-- An operation whose names are names of a good instruction or good names is good. -/
theorem namesOK_of_sub {j i : Linstr} (hi : NamesOK i)
    (h : ∀ n ∈ instrNames j.li_i, n ∈ instrNames i.li_i ∨ GoodName n) : NamesOK j := by
  intro n hn
  rcases h n hn with h | h
  · exact hi n h
  · exact h

/-- A good instruction whose first source is a register is good before the fold. -/
theorem foldOK_of_reg {j : Linstr} (h : NamesOK j)
    (hr : ∀ ds o ss, j.li_i = .Lopn ds o ss → ∀ a ∈ ss.head?, ∃ y, a = .reg y) : FoldOK j := by
  refine ⟨h, fun d B x sc he => ?_, fun d B x sc vn he => ?_, fun d B off he => ?_,
    fun d B off vn he => ?_⟩ <;>
  · obtain ⟨y, hy⟩ := hr _ _ _ he _ rfl
    cases hy

/-- **A body of good instructions has every cell name at the base `R14`.** -/
theorem cellBaseScratch_of_namesOK {b : Lcmd} (h : ∀ j ∈ b, NamesOK j) : CellBaseScratch b := by
  intro A o hm
  obtain ⟨j, hj, hn⟩ := List.mem_flatMap.mp hm
  exact (h j hj _ hn).1 A o rfl

/-- **A body of good instructions reads no stack-argument name.** -/
theorem stackReadFreeB_of_namesOK {b : Lcmd} (h : ∀ j ∈ b, NamesOK j) :
    stackReadFreeB b = true := by
  unfold stackReadFreeB
  refine List.all_eq_true.mpr fun j hj => ?_
  split
  · rename_i d s hs
    have hn : s ∈ instrNames j.li_i := by
      unfold JasminLsemAddrMem.slotMov? at hs
      split at hs
      · rename_i dst opn src he
        split at hs
        · split at hs
          · cases hs
          · simp only [Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨-, rfl⟩ := hs
            rw [he]
            simp [instrNames, JasminLsemExportRewrites.opNames]
        · cases hs
      · cases hs
    simp [(h j hj s hn).2]
  · rfl

/-- Sublists keep a predicate of every instruction. -/
theorem forall_sublist {P : Linstr → Prop} {b b' : Lcmd} (hs : b'.Sublist b)
    (h : ∀ j ∈ b, P j) : ∀ j ∈ b', P j :=
  fun j hj => h j (hs.subset hj)

/-! ## 3. The load CSE and the optimiser -/

section Opt

open CatCrypt.Crypto.Optimizer.LoadCSE
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate (isFactSrc copyPropagateBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass (OpRw RwClosed preLoad
  forall_preLoad forall_optimizeBasicBlocks)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (optimizeBasicBlocks)

/-- The environment of the load CSE after an instruction keeps good holders, when the
    instruction is good. -/
theorem stepLoad_env_good (h : LoadEnv) (i : Linstr) (hh : ∀ p ∈ h, GoodName p.2)
    (hi : NamesOK i) : ∀ p ∈ (stepLoad h i).2, GoodName p.2 := by
  cases hr : asWideReload i.li_i with
  | none =>
    rw [stepLoad_env_of_not_wideReload h i hr]
    intro p hp
    exact hh p (mem_foldl_killReg _ _ _ (mem_foldl_killSlot _ _ _ hp).1).1
  | some dsm =>
    obtain ⟨d, s, mn⟩ := dsm
    rw [stepLoad_env_of_wideReload h i hr]
    intro p hp
    rcases CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad.mem_set hp with
      ⟨hmem, _⟩ | rfl
    · exact hh p (mem_killReg (mem_killSlot hmem).1).1
    · obtain ⟨he, -⟩ := asWideReload_eq hr
      exact hi d (by rw [he]; simp [instrNames, JasminLsemExportRewrites.opNames])

/-- The instruction of the load CSE at a good instruction under good holders is good before
    the fold, when the instruction is. -/
theorem stepLoad_foldOK (h : LoadEnv) (i : Linstr) (hh : ∀ p ∈ h, GoodName p.2)
    (hi : FoldOK i) : FoldOK (stepLoad h i).1 := by
  rcases stepLoad_cases h i with he | ⟨d, s, r, mn, ha, hf, -, he⟩
  · rw [he]; exact hi
  · rw [he]
    obtain ⟨hw, -⟩ := asWideReload_eq ha
    have hr : GoodName r := hh (s, r)
      (CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad.mem_of_find hf)
    refine foldOK_of_reg (fun n hn => ?_) (fun ds o ss he' a ha' => ?_)
    · simp only [instrNames, JasminLsemExportRewrites.opNames, List.cons_append, List.nil_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl
      · exact hi.1 n (by rw [hw]; simp [instrNames, JasminLsemExportRewrites.opNames])
      · exact hr
    · simp only [LinstrR.Lopn.injEq] at he'
      obtain ⟨-, -, rfl⟩ := he'
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha'
      exact ⟨r, ha'.symm⟩

/-- **The load CSE keeps `FoldOK`.** -/
theorem foldOK_loadCSEAux : ∀ (b : Lcmd) (h : LoadEnv), (∀ p ∈ h, GoodName p.2) →
    (∀ j ∈ b, FoldOK j) → ∀ j ∈ loadCSEAux h b, FoldOK j
  | [], _, _, _ => by simp
  | i :: is, h, hh, hb => by
    rw [loadCSEAux_cons]
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact stepLoad_foldOK h i hh (hb i List.mem_cons_self)
    · exact foldOK_loadCSEAux is _
        (stepLoad_env_good h i hh (hb i List.mem_cons_self).1)
        (fun j hj => hb j (List.mem_cons_of_mem _ hj)) j hj

theorem foldOK_loadCSE {b : Lcmd} (hb : ∀ j ∈ b, FoldOK j) : ∀ j ∈ loadCSE b, FoldOK j := by
  rw [loadCSE_eq]
  exact foldOK_loadCSEAux b [] (by simp) hb

/-- A rewritten source that is no register is the source itself. -/
theorem opRw_eq_of_not_reg {dsts : List LOperand} {a a' : LOperand} (h : OpRw dsts a a')
    (hn : ∀ y, a' ≠ .reg y) (hi : ∀ v, a' ≠ .imm v) : a' = a := by
  rcases h with h | ⟨u, -, hf, -⟩
  · exact h
  · cases a' with
    | reg y => exact absurd rfl (hn y)
    | imm v => exact absurd rfl (hi v)
    | arr _ _ => cases hf
    | arrIdx _ _ _ => cases hf

/-- A rewritten source that is a register is the rewrite of a register. -/
theorem opRw_reg {dsts : List LOperand} {a : LOperand} {v : String} (h : OpRw dsts a (.reg v)) :
    ∃ u, a = .reg u := by
  rcases h with h | ⟨u, rfl, -, -⟩
  · exact ⟨v, h.symm⟩
  · exact ⟨u, rfl⟩

/-- **`FoldOK` is closed under the source rewrites of the copy propagation.** -/
theorem foldOK_rwClosed : RwClosed FoldOK := by
  intro i dsts opn srcs g hi he hg
  refine ⟨fun n hn => ?_, fun d B x sc he' => ?_, fun d B x sc vn he' => ?_,
    fun d B off he' => ?_, fun d B off vn he' => ?_⟩
  · rcases mem_instrNames_lopn.mp hn with ⟨a, ha, hn⟩ | ⟨a', ha', hn⟩
    · exact hi.1 n (by rw [he]; exact mem_instrNames_lopn.mpr (Or.inl ⟨a, ha, hn⟩))
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
      rcases hg a with h | ⟨u, -, hf, -⟩
      · rw [h] at hn
        exact hi.1 n (by rw [he]; exact mem_instrNames_lopn.mpr (Or.inr ⟨a, ha, hn⟩))
      · cases hga : g a with
        | reg s =>
          rw [hga] at hf hn
          simp only [JasminLsemExportRewrites.opNames, List.mem_singleton] at hn
          subst hn
          exact goodName_of_physGP hf
        | imm _ => rw [hga] at hn; simp [JasminLsemExportRewrites.opNames] at hn
        | arr _ _ => rw [hga] at hf; cases hf
        | arrIdx _ _ _ => rw [hga] at hf; cases hf
  all_goals
    dsimp only at he'
    simp only [LinstrR.Lopn.injEq] at he'
    obtain ⟨rfl, rfl, hs⟩ := he'
    rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, srcs⟩⟩⟩ <;>
      simp only [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq, and_false,
        List.nil_eq, and_true] at hs
  · have ha := opRw_eq_of_not_reg (hg a) (by rw [hs]; simp) (by rw [hs]; simp)
    exact hi.2.1 _ _ _ _ (by rw [he, ← ha, hs])
  · have ha := opRw_eq_of_not_reg (hg a) (by rw [hs.1]; simp) (by rw [hs.1]; simp)
    obtain ⟨u, rfl⟩ := opRw_reg (hs.2 ▸ hg b)
    exact hi.2.2.1 _ _ _ _ u (by rw [he, ← ha, hs.1])
  · have ha := opRw_eq_of_not_reg (hg a) (by rw [hs]; simp) (by rw [hs]; simp)
    exact hi.2.2.2.1 _ _ _ (by rw [he, ← ha, hs])
  · have ha := opRw_eq_of_not_reg (hg a) (by rw [hs.1]; simp) (by rw [hs.1]; simp)
    obtain ⟨u, rfl⟩ := opRw_reg (hs.2 ▸ hg b)
    exact hi.2.2.2.2 _ _ _ u (by rw [he, ← ha, hs.1])

/-- **The basic-block optimiser keeps `FoldOK`.** -/
theorem foldOK_optimizeBasicBlocks {b : Lcmd} (h : ∀ j ∈ b, FoldOK j) :
    ∀ j ∈ optimizeBasicBlocks b, FoldOK j :=
  forall_optimizeBasicBlocks h fun _ _ _ hs => foldOK_loadCSE (forall_preLoad foldOK_rwClosed hs)

end Opt

/-! ## 4. The constant-index fold -/

section Fold

open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold (foldCore_getElem? foldInstr_cases
  spellMemInstr_cases)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass (forall_dropDeadImmBody)

/-- **The constant-index fold keeps `FoldOK`**: a folded load or store has the names of its
    access and the base of its access as the base of its displacement source. -/
theorem foldOK_constIndexFoldBody {b : Lcmd} (h : ∀ j ∈ b, FoldOK j) :
    ∀ j ∈ constIndexFoldBody b, FoldOK j := by
  intro j hj
  unfold constIndexFoldBody at hj
  dsimp only at hj
  split at hj
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hj
    obtain ⟨i, e, h1, h2, -⟩ := foldCore_getElem? _ _ b [] k _ (List.getElem?_eq_getElem hk)
    have hi := h i (List.mem_of_getElem? h1)
    rw [h2]
    rcases foldInstr_cases _ e i.li_i with hf | ⟨d, B, x, sc, off, he, hf⟩ |
        ⟨d, B, x, sc, vn, off, he, hf⟩ | ⟨d, x, n, he, hf, -⟩
    · rw [hf]
      exact hi
    · rw [hf]
      have hB : B = "R14" := hi.2.1 _ _ _ _ he
      refine ⟨fun n hn => hi.1 n ?_, fun _ _ _ _ he' => by simp at he',
        fun _ _ _ _ _ he' => by simp at he', fun d' B' off' he' => ?_,
        fun _ _ _ _ he' => by simp at he'⟩
      · simp only [instrNames, JasminLsemExportRewrites.opNames, List.cons_append, List.nil_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hn
        subst hn
        rw [he]
        simp [instrNames, JasminLsemExportRewrites.opNames]
      · simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.arr.injEq] at he'
        rw [← he'.2.2.1.1, hB]
    · rw [hf]
      have hB : B = "R14" := hi.2.2.1 _ _ _ _ _ he
      refine ⟨fun n hn => hi.1 n ?_, fun _ _ _ _ he' => by simp at he',
        fun _ _ _ _ _ he' => by simp at he', fun _ _ _ he' => by simp at he',
        fun d' B' off' vn' he' => ?_⟩
      · simp only [instrNames, JasminLsemExportRewrites.opNames, List.cons_append, List.nil_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hn
        rw [he]
        simp only [instrNames, JasminLsemExportRewrites.opNames, List.cons_append, List.nil_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false]
        tauto
      · simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.arr.injEq] at he'
        rw [← he'.2.2.1.1, hB]
    · rw [hf]
      refine ⟨fun n' hn => hi.1 n' ?_, fun _ _ _ _ he' => by simp at he',
        fun _ _ _ _ _ he' => by simp at he', fun _ _ _ he' => by simp at he',
        fun _ _ _ _ he' => by simp at he'⟩
      simp only [instrNames, JasminLsemExportRewrites.opNames, List.cons_append, List.nil_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hn
      subst hn
      rw [he]
      simp [instrNames, JasminLsemExportRewrites.opNames]
  · exact h j hj

/-- **The fold, the dead-move elimination and the spelling give good instructions** on a
    body of `FoldOK` instructions: the spelling names the cell `memName B off` of a
    displacement source at the base `B = R14`. -/
theorem namesOK_foldIndexedBody {b : Lcmd} (h : ∀ j ∈ b, FoldOK j) :
    ∀ j ∈ foldIndexedBody b, NamesOK j := by
  have h1 := forall_dropDeadImmBody (foldOK_constIndexFoldBody h)
  intro j hj
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
  have hi' := h1 i hi
  rcases spellMemInstr_cases i.li_i with he | ⟨d, B, off, he, o, hs, -⟩ |
      ⟨d, B, off, vn, he, o, hs, -⟩
  · intro n hn
    exact hi'.1 n (by rw [he] at hn; exact hn)
  · have hB : B = "R14" := hi'.2.2.2.1 _ _ _ he
    subst hB
    intro n hn
    dsimp only at hn
    rw [hs] at hn
    simp only [instrNames, JasminLsemExportRewrites.opNames, List.cons_append, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · exact hi'.1 n (by rw [he]; simp [instrNames, JasminLsemExportRewrites.opNames])
    · exact goodName_memName_R14 off
  · have hB : B = "R14" := hi'.2.2.2.2 _ _ _ _ he
    subst hB
    intro n hn
    dsimp only at hn
    rw [hs] at hn
    simp only [instrNames, JasminLsemExportRewrites.opNames, List.cons_append, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · exact goodName_memName_R14 off
    · exact hi'.1 n (by rw [he]; simp [instrNames, JasminLsemExportRewrites.opNames])

end Fold

/-! ## 5. The register re-allocation -/

section Realloc

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg (annotate_fst)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocLeak (Piece.toLcmd pieces_flatten)

/-- The names of a fragment instruction: its destination and the names of its sources. -/
theorem mem_instrNames_toL {i : FI} {n : String} :
    n ∈ instrNames i.toL.li_i ↔ n = i.d ∨ ∃ a ∈ i.srcs, n ∈ JasminLsemExportRewrites.opNames a := by
  simp [FI.toL, FI.toR, instrNames, JasminLsemExportRewrites.opNames, List.mem_flatMap]

/-- A map of locations whose values are good. -/
def CurGood (m : Cur) : Prop := ∀ k v : String, (m[k]? : Option String) = some v → GoodName v

theorem curGood_empty : CurGood ({} : Cur) := by
  intro k v h
  simp at h

theorem curGood_insert {m : Cur} (hm : CurGood m) {k c : String} (hc : GoodName c) :
    CurGood (m.insert k c) := by
  intro k' v h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · cases h; exact hc
  · exact hm k' v h

/-- The location of a name under a good map is the name or a good name. -/
theorem look_cases {m : Cur} (hm : CurGood m) (n : String) : look m n = n ∨ GoodName (look m n) := by
  unfold look
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases h : m[n]? with
  | none => exact Or.inl rfl
  | some v => exact Or.inr (hm n v h)

/-- The names of a renamed operand are names of the operand or good names. -/
theorem opNames_renOp {m : Cur} (hm : CurGood m) {abi : IsaAbi} (a : LOperand) :
    ∀ n ∈ JasminLsemExportRewrites.opNames (renOp m a abi), n ∈ JasminLsemExportRewrites.opNames a ∨ GoodName n := by
  intro n hn
  cases a with
  | reg x =>
    by_cases hl : isLoc x abi = true
    · simp only [renOp, hl, ite_true, JasminLsemExportRewrites.opNames, List.mem_singleton] at hn
      subst hn
      rcases look_cases hm x with h | h
      · exact Or.inl (by rw [h]; simp [JasminLsemExportRewrites.opNames])
      · exact Or.inr h
    · simp only [renOp, hl, Bool.false_eq_true, ite_false] at hn
      exact Or.inl hn
  | _ => exact Or.inl hn

/-- A materialized instruction of `goAcc` at a good destination is good. -/
theorem namesOK_mat {m : Cur} (hm : CurGood m) {abi : IsaAbi} {i : FI} (hi : NamesOK i.toL)
    {c : String} (hc : GoodName c) :
    NamesOK (⟨i.ii, c, i.opn, i.srcs.map (fun o => renOp m o abi)⟩ : FI).toL := by
  intro n hn
  rcases mem_instrNames_toL.mp hn with rfl | ⟨a', ha', hn⟩
  · exact hc
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    rcases opNames_renOp hm a n hn with h | h
    · exact hi n (mem_instrNames_toL.mpr (Or.inr ⟨a, ha, h⟩))
    · exact h

/-- **The checked materialization of a run keeps good instructions**, when every register of
    the pool is good. -/
theorem goAcc_namesOK {abi : IsaAbi} (hpool : ∀ c, isPool c abi = true → GoodName c)
    (lend : List String) :
    ∀ (ann : List (FI × List String)) (m : Cur) (cs : List String) (acc out : List FI),
      goAcc lend m ann cs acc abi = some out → CurGood m → (∀ j ∈ acc, NamesOK j.toL) →
      (∀ p ∈ ann, NamesOK p.1.toL) → ∀ j ∈ out, NamesOK j.toL := by
  intro ann
  induction ann with
  | nil =>
    intro m cs acc out h _ hacc _ j hj
    cases cs with
    | cons _ _ => simp [goAcc] at h
    | nil =>
      simp only [goAcc] at h
      split at h
      · cases h; exact hacc j (by simpa using hj)
      · cases h
  | cons p rest ih =>
    intro m cs acc out h hm hacc hann j hj
    obtain ⟨i, la⟩ := p
    have hi : NamesOK i.toL := hann (i, la) List.mem_cons_self
    have hrest : ∀ p ∈ rest, NamesOK p.1.toL := fun p hp => hann p (List.mem_cons_of_mem _ hp)
    have hd : GoodName i.d := hi i.d (mem_instrNames_toL.mpr (Or.inl rfl))
    cases cs with
    | nil => simp [goAcc] at h
    | cons c cs =>
      simp only [goAcc] at h
      split at h
      · split at h
        · split at h
          · rename_i hok
            have hc : GoodName c := by
              simp only [Bool.and_eq_true, okLoc, Bool.or_eq_true, beq_iff_eq] at hok
              rcases hok.1 with h' | h'
              · exact hpool c h'
              · rw [h']; exact hd
            split at h
            · exact ih _ cs acc out h (curGood_insert hm hc) hacc hrest j hj
            · split at h
              · exact ih _ cs acc out h hm hacc hrest j hj
              · split at h
                · refine ih _ cs _ out h (curGood_insert hm hc) ?_ hrest j hj
                  intro k hk
                  rcases List.mem_cons.mp hk with rfl | hk
                  · exact namesOK_mat hm hi hc
                  · exact hacc k hk
                · cases h
          · cases h
        · split at h
          · refine ih _ cs _ out h hm ?_ hrest j hj
            intro k hk
            rcases List.mem_cons.mp hk with rfl | hk
            · exact namesOK_mat hm hi hd
            · exact hacc k hk
          · cases h
      · cases h

/-- **The re-allocation of a run keeps good instructions.** -/
theorem reallocRun_namesOK {abi : IsaAbi} (hpool : ∀ c, isPool c abi = true → GoodName c)
    (lend : List String) (is : List FI) (h : ∀ i ∈ is, NamesOK i.toL) :
    ∀ j ∈ reallocRun lend is abi, NamesOK j.toL := by
  unfold reallocRun reallocWith
  split
  · rename_i out hf
    obtain ⟨cs, _, hcs⟩ := List.exists_of_findSome?_eq_some hf
    exact goAcc_namesOK hpool lend _ {} cs [] out hcs curGood_empty (by simp)
      (fun p hp => h p.1 (annotate_fst lend is p hp))
  · exact h

/-- At `x86Abi` every register of the pool is good. -/
theorem goodName_of_isPool_x86 {c : String} (h : isPool c = true) : GoodName c := by
  rw [isPool_x86] at h
  simp only [Bool.and_eq_true] at h
  exact goodName_of_physGP h.1.1

/-- **The register re-allocation keeps good instructions.** -/
theorem namesOK_reallocBody (res : List String) {b : Lcmd} (h : ∀ j ∈ b, NamesOK j) :
    ∀ j ∈ reallocBody res b, NamesOK j := by
  have hps : ∀ p ∈ pieces b, ∀ j ∈ Piece.toLcmd p, NamesOK j := by
    intro p hp j hj
    exact h j (by
      rw [← pieces_flatten b]
      exact List.mem_flatten.mpr ⟨Piece.toLcmd p, List.mem_map_of_mem hp, hj⟩)
  unfold reallocBody
  dsimp only
  generalize pieces b = ps at hps
  induction ps with
  | nil => intro j hj; simp at hj
  | cons p ps ih =>
    intro j hj
    have ih' := ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))
    rw [List.foldr_cons] at hj
    split at hj
    · rename_i is
      rcases List.mem_append.mp hj with hj | hj
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
        exact reallocRun_namesOK (fun _ hc => goodName_of_isPool_x86 hc) _ is
          (fun i hi => hps (.run is) (by simp) i.toL (List.mem_map_of_mem hi)) k hk
      · exact ih' j hj
    · rename_i li
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hps (.bar j) (by simp) j (by simp [Piece.toLcmd])
      · exact ih' j hj

end Realloc

/-! ## 6. The two-address legalisation, the compare reload and the frame trim -/

section Print

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi IsaData)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (legalizeInstr twoAddrBody
  scratchRoute scratchSave x86Data)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload (cmpReload cmpReloadI spillCmp?)

/-- The names of an operation whose operands are among the operands of another operation and
    registers of `X` are names of the other operation or names of `X`. -/
theorem names_of_subset {ds ss ds' ss' : List LOperand} {o o' : String} {X : List String}
    (h : ds ++ ss ⊆ ds' ++ ss' ++ X.map LOperand.reg) :
    ∀ n ∈ instrNames (.Lopn ds o ss), n ∈ instrNames (.Lopn ds' o' ss') ∨ n ∈ X := by
  intro n hn
  obtain ⟨a, ha, hn⟩ := List.mem_flatMap.mp hn
  rcases List.mem_append.mp (h ha) with h1 | h1
  · exact Or.inl (List.mem_flatMap.mpr ⟨a, h1, hn⟩)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h1
    simp only [JasminLsemExportRewrites.opNames, List.mem_singleton] at hn
    subst hn
    exact Or.inr hx

/-- **Every name of the legalisation of an instruction** is a name of the instruction, the
    scratch register or its save slot. -/
theorem names_legalizeInstr (ok : Bool) (i : Linstr) :
    ∀ r ∈ legalizeInstr ok i x86Data, ∀ n ∈ instrNames r.li_i,
      n ∈ instrNames i.li_i ∨ n ∈ [x86Data.tieScratch, scratchSave x86Data] := by
  intro r hr
  generalize hL : legalizeInstr ok i x86Data = L at hr
  unfold legalizeInstr at hL
  split at hL
  · rename_i d opn a b he
    rw [he]
    split at hL
    · split at hL
      · subst hL
        rw [List.mem_singleton] at hr
        subst hr
        rw [he]
        exact fun n hn => Or.inl hn
      · split at hL
        · split at hL
          · subst hL
            rw [List.mem_singleton] at hr
            subst hr
            exact names_of_subset (by simp [List.subset_def])
          · subst hL
            rw [List.mem_singleton] at hr
            subst hr
            rw [he]
            exact fun n hn => Or.inl hn
        · split at hL
          · subst hL
            rw [List.mem_singleton] at hr
            subst hr
            rw [he]
            exact fun n hn => Or.inl hn
          · split at hL
            · subst hL
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl
              · exact names_of_subset (by simp [List.subset_def])
              · exact names_of_subset (by simp [List.subset_def])
            · split at hL
              · subst hL
                rw [List.mem_singleton] at hr
                subst hr
                exact names_of_subset (by simp [List.subset_def])
              · split at hL
                · split at hL
                  all_goals
                    subst hL
                    simp only [scratchRoute, List.mem_cons, List.not_mem_nil, or_false] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
                      exact names_of_subset (by simp [List.subset_def])
                · subst hL
                  rw [List.mem_singleton] at hr
                  subst hr
                  rw [he]
                  exact fun n hn => Or.inl hn
    · subst hL
      rw [List.mem_singleton] at hr
      subst hr
      rw [he]
      exact fun n hn => Or.inl hn
  · subst hL
    rw [List.mem_singleton] at hr
    subst hr
    exact fun n hn => Or.inl hn

/-- The scratch register of the legalisation and its save slot are good. -/
theorem goodName_tieScratch : GoodName x86Data.tieScratch :=
  goodName_of_head (by decide) (by decide)

theorem goodName_scratchSave : GoodName (scratchSave x86Data) :=
  goodName_of_head (by decide) (by decide)

/-- **The two-address legalisation keeps good instructions.** -/
theorem namesOK_twoAddrBody {b : Lcmd} (h : ∀ j ∈ b, NamesOK j) :
    ∀ j ∈ twoAddrBody b x86Data, NamesOK j := by
  intro r hr
  obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
  intro n hn
  rcases names_legalizeInstr _ i r hr n hn with h' | h'
  · exact h i hi n h'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with rfl | rfl
    · exact goodName_tieScratch
    · exact goodName_scratchSave

/-- A compare on a spilled first operand is an operation on that operand. -/
theorem spillCmp?_eq {w : LinstrR} {abi : IsaAbi} {opn d : String} {s : LOperand}
    (h : spillCmp? w abi = some (opn, d, s)) : ∃ a, w = .Lopn [.reg d] opn [.reg a, s] := by
  unfold spillCmp? at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨_, rfl⟩
    · cases h
  · cases h

/-- **The compare reload keeps good instructions**, when its reload register is good. -/
theorem namesOK_cmpReload {abi : IsaAbi} (hab : GoodName abi.reload) {b : Lcmd}
    (h : ∀ j ∈ b, NamesOK j) : ∀ j ∈ cmpReload b abi, NamesOK j := by
  intro r hr
  obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
  unfold cmpReloadI at hr
  split at hr
  · rename_i opn d s heq
    obtain ⟨a, he⟩ := spillCmp?_eq heq
    have key : ∀ n, n ∈ instrNames i.li_i ∨ n ∈ [abi.reload] → GoodName n := by
      intro n hn
      rcases hn with hn | hn
      · exact h i hi n hn
      · rw [List.mem_singleton] at hn
        subst hn
        exact hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro n hn
      refine key n ?_
      rw [he]
      exact names_of_subset (by simp [List.subset_def]) n hn
    · intro n hn
      refine key n ?_
      rw [he]
      exact names_of_subset (by simp [List.subset_def]) n hn
  · rw [List.mem_singleton] at hr
    subst hr
    exact h r hi

/-- **The frame trim keeps a sublist.** -/
theorem frameTrim_sublist (b : Lcmd) : (frameTrim b).Sublist b :=
  List.filter_sublist

end Print

/-! ## 7. The high-product fusion -/

section Fuse

open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi

/-- A scratch environment whose held names are good. -/
def EnvGood (env : ScratchEnv) : Prop := ∀ p ∈ env, GoodName p.2

theorem envGood_kill {env : ScratchEnv} (h : EnvGood env) (d : String) :
    EnvGood (scratchKill env d) :=
  fun p hp => h p (List.mem_of_mem_filter hp)

theorem envGood_foldl_kill (ds : List String) {env : ScratchEnv} (h : EnvGood env) :
    EnvGood (ds.foldl scratchKill env) := by
  induction ds generalizing env with
  | nil => exact h
  | cons d ds ih => exact ih (envGood_kill h d)

theorem envGood_bind {env : ScratchEnv} (h : EnvGood env) {d v : String} (hv : GoodName v) :
    EnvGood (scratchBind env d v) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hv
  · exact h p (List.mem_of_mem_filter hp)

/-- The resolution of a good name under a good environment is good. -/
theorem goodName_scratchResolve {env : ScratchEnv} (h : EnvGood env) {r : String}
    (hr : GoodName r) : GoodName (scratchResolve env r) := by
  unfold scratchResolve
  split
  · rename_i a v hf
    exact h _ (List.mem_of_find?_eq_some hf)
  · exact hr

/-- A predicate kept by every step of a fold over a list holds at its end. -/
theorem foldl_inv {α β : Type} (f : β → α → β) (P : β → Prop) :
    ∀ (l : List α) (x : β), P x → (∀ y a, a ∈ l → P y → P (f y a)) → P (l.foldl f x)
  | [], _, hx, _ => hx
  | a :: l, x, hx, h => foldl_inv f P l (f x a) (h x a List.mem_cons_self hx)
      (fun y a' ha hy => h y a' (List.mem_cons_of_mem _ ha) hy)

/-- **The scratch step at a good instruction keeps a good environment.** -/
theorem envGood_scratchStep {env : ScratchEnv} (h : EnvGood env) {i : Linstr} (hi : NamesOK i) :
    EnvGood (scratchStep env i) := by
  unfold scratchStep
  split
  · rename_i dsts opn srcs he
    refine foldl_inv _ EnvGood _ env h ?_
    intro e d _ he'
    split
    · split
      · split
        · rename_i dn sn
          split
          · refine envGood_bind he' (goodName_scratchResolve h (hi sn ?_))
            rw [he]
            simp [instrNames, JasminLsemExportRewrites.opNames]
          · exact envGood_kill he' _
        · exact envGood_kill he' _
      · exact he'
    · exact he'
  · exact h

/-- The home of a low product at a good destination under a good environment is good. -/
theorem goodName_lowHome {env : ScratchEnv} (h : EnvGood env) {d s2 : String}
    (hd : GoodName d) : GoodName (lowHome env d s2) := by
  unfold lowHome
  split
  · exact goodName_scratchResolve h hd
  · exact hd

/-- An operation whose destinations are good registers and whose one source is a good
    register is good before the fold. -/
theorem foldOK_emit {ii : Nat} {ds : List LOperand} {o y : String}
    (hds : ∀ a ∈ ds, ∃ x, a = .reg x ∧ GoodName x) (hy : GoodName y) :
    FoldOK ⟨ii, .Lopn ds o [.reg y]⟩ := by
  refine foldOK_of_reg (fun n hn => ?_) (fun ds' o' ss he a ha => ?_)
  · rcases mem_instrNames_lopn.mp hn with ⟨a, ha, hn⟩ | ⟨a, ha, hn⟩
    · obtain ⟨x, rfl, hx⟩ := hds a ha
      simp only [JasminLsemExportRewrites.opNames, List.mem_singleton] at hn
      subst hn
      exact hx
    · simp only [List.mem_singleton] at ha
      subst ha
      simp only [JasminLsemExportRewrites.opNames, List.mem_singleton] at hn
      subst hn
      exact hy
  · simp only [LinstrR.Lopn.injEq] at he
    obtain ⟨-, -, rfl⟩ := he
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
    exact ⟨y, ha.symm⟩

theorem goodName_ite {c : Prop} [Decidable c] {x y : String} (hx : GoodName x)
    (hy : GoodName y) : GoodName (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem goodName_RDX : GoodName "RDX" := goodName_of_head (by decide) (by decide)
theorem goodName_R14 : GoodName "R14" := goodName_of_head (by decide) (by decide)
theorem goodName_R15 : GoodName "R15" := goodName_of_head (by decide) (by decide)
theorem goodName_reloadScratch : GoodName reloadScratch := goodName_R15
theorem goodName_reloadScratch2 : GoodName reloadScratch2 := goodName_R14

/-- The entries of a split of the pending list are entries of the list. -/
theorem mem_of_span {pend before after : List (String × String)} {f : String × String → Bool}
    {q : String × String} (hs : pend.span f = (before, q :: after)) :
    q ∈ pend ∧ ∀ p ∈ before ++ after, p ∈ pend := by
  rw [List.span_eq_takeWhile_dropWhile, Prod.mk.injEq] at hs
  have he := List.takeWhile_append_dropWhile (p := f) (l := pend)
  rw [hs.1, hs.2] at he
  refine ⟨by rw [← he]; simp, fun p hp => ?_⟩
  rw [← he]
  simp only [List.mem_append, List.mem_cons] at hp ⊢
  tauto

/-- Closes a goal `GoodName n` for a name built by conditionals from good names. -/
local macro "good_name" : tactic =>
  `(tactic| repeat' (first
    | assumption
    | exact goodName_RDX
    | exact goodName_R14
    | exact goodName_R15
    | exact goodName_reloadScratch
    | exact goodName_reloadScratch2
    | apply goodName_ite))

/-- Closes a goal `FoldOK j` for a move or `MULX` of good registers. -/
local macro "good_emit" : tactic =>
  `(tactic| (refine foldOK_emit (fun a ha => ?_) ?_ <;>
    first
      | (simp only [List.mem_cons, List.not_mem_nil, or_false] at ha;
          rcases ha with rfl | rfl <;> exact ⟨_, rfl, by good_name⟩)
      | good_name))

/-- **The high-product fusion keeps `FoldOK`**: it writes the operands of the high product,
    `RDX`, the reserved scratches and the recorded homes of low products. -/
theorem foldOK_fuseMulHiAux : ∀ (b : Lcmd) (env : ScratchEnv) (pend : List (String × String)),
    EnvGood env → (∀ p ∈ pend, GoodName p.1) → (∀ j ∈ b, FoldOK j) →
    ∀ j ∈ fuseMulHiAux true env pend b, FoldOK j
  | [], env, pend, _, _, _ => by rw [fuseMulHiAux]; simp
  | i :: rest, env, pend, he, hp, hb => by
    have hi := hb i List.mem_cons_self
    have hrest : ∀ j ∈ rest, FoldOK j := fun j hj => hb j (List.mem_cons_of_mem _ hj)
    have he' := envGood_scratchStep he hi.1
    intro j hj
    rw [fuseMulHiAux] at hj
    split at hj
    · rename_i d opn s1 s2 heq
      have hn : ∀ n, n = d ∨ n = s1 ∨ n = s2 → GoodName n := by
        intro n hn
        refine hi.1 n ?_
        rw [heq]
        simp only [instrNames, JasminLsemExportRewrites.opNames, List.cons_append, List.nil_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false]
        tauto
      have hd := hn d (Or.inl rfl)
      have hs1 := hn s1 (Or.inr (Or.inl rfl))
      have hs2 := hn s2 (Or.inr (Or.inr rfl))
      split at hj
      · rcases List.mem_cons.mp hj with rfl | hj
        · exact hi
        · refine foldOK_fuseMulHiAux rest _ _ he' ?_ hrest j hj
          intro p hp'
          rcases List.mem_cons.mp hp' with rfl | hp'
          · exact goodName_ite (goodName_scratchResolve he hd) hd
          · exact hp p hp'
      · split at hj
        · dsimp only at hj
          split at hj
          · rename_i before loDst k after hspan
            obtain ⟨hq, hba⟩ := mem_of_span hspan
            have hlo : GoodName loDst := hp _ hq
            have hpend : ∀ p ∈ before ++ after, GoodName p.1 := fun p h' => hp p (hba p h')
            split at hj
            · split at hj
              · rcases List.mem_append.mp hj with hj | hj
                · unfold squareSite at hj
                  split at hj <;>
                    simp only [List.cons_append, List.nil_append, List.mem_cons,
                      List.not_mem_nil, or_false] at hj <;>
                    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> good_emit
                · exact foldOK_fuseMulHiAux rest _ _ (envGood_foldl_kill _ he') hpend hrest j hj
              · rcases List.mem_cons.mp hj with rfl | hj
                · exact hi
                · exact foldOK_fuseMulHiAux rest _ _ he' hp hrest j hj
            · split at hj
              · rcases List.mem_cons.mp hj with rfl | hj
                · exact hi
                · exact foldOK_fuseMulHiAux rest _ _ he' hp hrest j hj
              · have hs2r : GoodName (if (true && s2 == "RDX") = true then reloadScratch
                    else if (LOperand.reg s2).isSpill = true then reloadScratch2 else s2) :=
                  goodName_ite goodName_reloadScratch (goodName_ite goodName_reloadScratch2 hs2)
                simp only [List.mem_append, List.mem_cons] at hj
                rcases hj with hj | rfl | hj | rfl | (hj | hj) | hj
                · simp only [ite_true, List.mem_singleton] at hj
                  subst hj
                  good_emit
                · good_emit
                · split at hj
                  · rw [List.mem_singleton] at hj
                    subst hj
                    good_emit
                  · simp at hj
                · good_emit
                · split at hj
                  · rw [List.mem_singleton] at hj
                    subst hj
                    good_emit
                  · simp at hj
                · split at hj
                  · rw [List.mem_singleton] at hj
                    subst hj
                    good_emit
                  · simp at hj
                · exact foldOK_fuseMulHiAux rest _ _ (envGood_foldl_kill _ he') hpend hrest j hj
          · rcases List.mem_cons.mp hj with rfl | hj
            · exact hi
            · exact foldOK_fuseMulHiAux rest _ _ he' hp hrest j hj
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact hi
          · exact foldOK_fuseMulHiAux rest _ _ he' hp hrest j hj
    · rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact foldOK_fuseMulHiAux rest _ _ he' hp hrest j hj
  termination_by b => b.length

end Fuse

/-! ## 8. The printed body -/

section Chain

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate (postBody printedBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiBody)

/-- The dead-write elimination keeps a sublist of the body. -/
theorem deadWriteRet_sublist (b : Lcmd) : (deadWriteRet b).Sublist b := by
  unfold deadWriteRet
  split
  · next r hr =>
    split
    · conv_rhs => rw [← List.dropLast_append_getLast? r hr]
      exact (X86Backend.OwnedLprogTV.dropDeadWriteBody_sublist _).append (List.Sublist.refl _)
    · exact List.Sublist.refl _
  · exact List.Sublist.refl _

/-- **The fusion post-pass keeps `FoldOK`.** -/
theorem foldOK_postBody {b0 : Lcmd} (h : ∀ j ∈ b0, FoldOK j) : ∀ j ∈ postBody b0, FoldOK j :=
  forall_sublist (deadWriteRet_sublist _)
    (foldOK_fuseMulHiAux b0 [] [] (by simp [EnvGood]) (by simp) h)

/-- **Every instruction of the trimmed printed body of an allocated body of `FoldOK`
    instructions is good.** -/
theorem namesOK_printed (res : List String) {b0 : Lcmd} (h : ∀ j ∈ b0, FoldOK j) :
    ∀ j ∈ frameTrim (printedBody res b0), NamesOK j :=
  forall_sublist (frameTrim_sublist _)
    (namesOK_cmpReload (goodName_of_head (by decide) (by decide))
      (namesOK_twoAddrBody (namesOK_reallocBody res (namesOK_foldIndexedBody
        (foldOK_optimizeBasicBlocks (foldOK_postBody h))))))

end Chain

/-! ## 9. The printed body of the field domain -/

section Field

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate (printedBody
  firstBody_printedLprog_regionPostFuse)
open CatCrypt.Crypto.Hax (HaxModule)

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **The allocated function of a member of the field domain is of `FoldOK` instructions**:
    every instruction of every function of the program that the allocation stage
    `regionAllocC` gives on the narrowed output of the chain is `FoldOK`. -/
def AllocFoldOK (e : _root_.Hax.TExpr) (σ : AbiLayout) (fname : String) : Prop :=
  ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
    (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0])
    (P0 : Lprog) (c : List (String × String)),
    haxEntry.chainNF (HaxModule.single e) σ = some ⟨t0, q⟩ →
    NarrowWords.narrowPrep q = some q' →
    regionAllocC (nfAbiNames fname σ) (legalizeRegion q') none (regionWebsEx σ exportReg)
      = some (P0, c) →
    ∀ nf ∈ P0.lp_funcs, ∀ j ∈ nf.2.lfd_body, FoldOK j

/-- The program of the allocation stage has one function. -/
theorem regionAllocC_lp_funcs (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (ex : List String) {x : Lprog × List (String × String)}
    (h : regionAllocC a p none ex = some x) : ∃ f, x.1.lp_funcs = [(a.fname, f)] := by
  unfold regionAllocC at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨r0, -, fd0, -, rfl⟩ := h
  exact ⟨_, rfl⟩

/-- **The printed body of a member is the trimmed printed body of its allocated function.** -/
theorem fieldBody_printedBody (hB : FieldBody e σ fname b t r cert) :
    ∃ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
      (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0])
      (P0 : Lprog) (f : Lfundef),
      haxEntry.chainNF (HaxModule.single e) σ = some ⟨t0, q⟩ ∧
      NarrowWords.narrowPrep q = some q' ∧
      regionAllocC (nfAbiNames fname σ) (legalizeRegion q') none (regionWebsEx σ exportReg)
        = some (P0, cert) ∧
      P0.lp_funcs = [(fname, f)] ∧ b = frameTrim (printedBody f.lfd_res f.lfd_body) := by
  obtain ⟨t0, q, q', r0, P, hq, hq', -, -, hP, hb, -⟩ := hB
  unfold regionLprogC at hP
  obtain ⟨x, hx, hxe⟩ := Option.map_eq_some_iff.mp hP
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl⟩ := hxe
  obtain ⟨f, hf⟩ := regionAllocC_lp_funcs _ _ _ hx
  refine ⟨t0, q, q', x.1, f, hq, hq', hx, hf, ?_⟩
  rw [firstBody_regionPrinted, firstBody_printedLprog_regionPostFuse hf] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  exact hb.symm

/-- **Every instruction of the printed body of a member is good**, when its allocated
    function is of `FoldOK` instructions. -/
theorem namesOK_fieldBody (hB : FieldBody e σ fname b t r cert) (hA : AllocFoldOK e σ fname) :
    ∀ j ∈ b, NamesOK j := by
  obtain ⟨t0, q, q', P0, f, hq, hq', hx, hf, hb⟩ := fieldBody_printedBody hB
  have hmem : (fname, f) ∈ P0.lp_funcs := by
    rw [hf]
    exact List.mem_singleton_self _
  have hf0 : ∀ j ∈ f.lfd_body, FoldOK j := hA t0 q q' P0 cert hq hq' hx (fname, f) hmem
  intro j hj
  rw [hb] at hj
  exact namesOK_printed f.lfd_res hf0 j hj

/-- **`CellBaseScratch` on the printed body of a member** from its allocated function. -/
theorem cellBaseScratch_of_allocFoldOK (hB : FieldBody e σ fname b t r cert)
    (hA : AllocFoldOK e σ fname) : CellBaseScratch b :=
  cellBaseScratch_of_namesOK (namesOK_fieldBody hB hA)

/-- **The printed body of a member reads no stack-argument name**, from its allocated
    function. -/
theorem stackReadFreeB_of_allocFoldOK (hB : FieldBody e σ fname b t r cert)
    (hA : AllocFoldOK e σ fname) : stackReadFreeB b = true :=
  stackReadFreeB_of_namesOK (namesOK_fieldBody hB hA)

/-- **Stage `G20` on `fieldDomB'`** when the allocated function is of `FoldOK` instructions. -/
theorem fieldDom_cellNamesRB_of_allocFoldOK (h : fieldDomB' e σ = true)
    (hB : FieldBody e σ fname b t r cert) (hA : AllocFoldOK e σ fname) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "cellNamesRB" :=
  fieldDom_cellNamesRB_of_cellBase h hB (cellBaseScratch_of_allocFoldOK hB hA)

end Field

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
