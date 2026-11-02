/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInit

@[expose] public section

/-!
# The sorted certificate of the region export

The coalescing step of the allocation input renames the array positions of the code
(`renArr σ`). `renArr σ` renames the whole names of the code only when `σ` fixes the names at
its register positions, a condition the export does not satisfy: `exportR` names registers by
depth and reuses a name both as a register and as an array across sibling scopes. This module
carries a certificate of definite assignment across that step for every `σ`, through the sorted
namespace of array positions, and composes it with the later steps of the input of the
allocation (`allocChain`, `regionAllocCode_chain`).

## The sorted namespace

`tagA x = "@" ++ x` names the array position `x`, and `untag σ` sends `@x` to `σ x` and keeps
every untagged name. The renamings of array positions compose (`renArr_renArr`), so
`renArr σ = renArr (untag σ) ∘ renArr tagA`. On code whose instructions are no call shadows
and mention no tagged name (`NoTag`), the names `renArr σ i` reads and writes are the images
under `untag σ` of those of `renArr tagA i` (`names_renArr_factor`); without a compile-time
array element among the sources of an array zeroing, `renArr σ i` is
`renRM (untag σ) (renArr tagA i)` (`renArr_factor`). A certificate of the tagged code
`C.map (renArr tagA)` therefore gives, by `Cert.map`, a certificate of `C.map (renArr σ)` for
every `σ` (`Cert.renArrS`).

## The certificate of the tagged export

A binding of a stack-array type is read and written at its array positions, and every other
binding at its register positions, so in the tagged code a binding has one name, its sorted
name `sortName t x` (`x` for a register type, `tagA x` for an array type). The block
judgement of the tagged export (`exportR_blkS`) follows `RegionExportDefInit.exportR_blk`
with the bindings in scope at their sorted names (`InScopeS`), the argument names in both
namespaces (`ArgS`), and the returned operands at the sorted names of their types (`ResNS`).
The array moves of the frames are the moves of the tagged array names (`map_renArr_arrMoves`);
every other frame instruction is its own renaming.

## Main results

* `renArr_factor`, `Cert.renArrS`: the factorization and the certificate of the renamed code.
* `renArr_of_cmp`: a compare is its own renaming.
* `renArr_nest_noGoto_regDsts`: the renaming keeps the nesting, the absence of unconditional
  jumps and the register destinations.
* `exportR_blkS`, `exportR_certS`: the certificate of the tagged export.
* `exportR_regReads`: the register reads of the export are written as registers on every
  path (`RegReads`); `RegionExp.cert_of_exportR`, `RegionExp.defInit_of_exportR` and
  `RegionExp.certS_of_exportR` discharge `RegReads` through it.
* `Cert.regionLprogCopyS`, `cert_regionCoCodeS`: the certificates of the tagged code with the
  array result copy.
* `allocChain`, `regionAllocCode_chain`: definite assignment, forward reachability and loop
  headers of the input of the allocation from a certificate of the tagged code.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInitSort

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findLabelMem IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames defNames
  jumpLabel?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webSuccs)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaData shadowCall?
  eq_callShadow_of_shadowCall?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renLinstrR
  renOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr renLoad renStore
  renZero renStoreImm renCallW renOpA renCallW_of_none)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionCoComplete (NoShadow noShadow_movI
  noShadow_labelI noShadow_x86Guards noShadow_seedMoves noShadow_parMoves
  noShadow_advanceOps noShadow_flagWord x86Data_guardsNoShadow noShadow_bindOps)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (movesOf)

/-! ## 1. The tagged namespace -/

/-- The name of the array position `x` in the sorted namespace: `x` prefixed by `@`. -/
def tagA (x : String) : String := "@" ++ x

/-- A name of the namespace of array positions: its first character is `@`. -/
def IsTag (x : String) : Prop := x.toList.head? = some '@'

/-- The renaming `σ` read on the sorted namespace: a tagged name `@x` is sent to `σ x`, and
    every other name is kept. -/
def untag (σ : String → String) (x : String) : String :=
  match x.toList with
  | '@' :: rest => σ (String.ofList rest)
  | _ => x

theorem toList_tagA (x : String) : (tagA x).toList = '@' :: x.toList := by
  rw [tagA, String.toList_append]
  rfl

theorem isTag_tagA (x : String) : IsTag (tagA x) := by
  simp [IsTag, toList_tagA]

theorem untag_tagA (σ : String → String) (x : String) : untag σ (tagA x) = σ x := by
  simp only [untag, toList_tagA, String.ofList_toList]

theorem untag_of_not {σ : String → String} {x : String} (h : ¬ IsTag x) : untag σ x = x := by
  unfold untag
  split
  · next rest hx => exact absurd (by simp [IsTag, hx]) h
  · rfl

theorem tagA_injective : Function.Injective tagA := by
  intro a b h
  have h' := congrArg String.toList h
  rw [toList_tagA, toList_tagA, List.cons.injEq] at h'
  exact String.toList_inj.mp h'.2

/-! ## 2. The factorization of the renaming of array positions -/

theorem renOperand_fix {τ : String → String} {o : LOperand} (h : ∀ x ∈ opNames o, τ x = x) :
    renOperand τ o = o := by
  cases o <;> simp_all [renOperand, opNames]

/-- A renaming that fixes every name of an instruction leaves it unchanged. -/
theorem renLinstrR_fix {τ : String → String} {w : LinstrR}
    (h : ∀ x ∈ defNames w ++ useNames w, τ x = x) : renLinstrR τ w = w := by
  cases w with
  | Lopn ds o ss =>
      have hd : ds.map (renOperand τ) = ds := by
        conv_rhs => rw [← List.map_id ds]
        exact List.map_congr_left fun a ha => renOperand_fix fun x hx => h x (by
          rw [defNames_Lopn, useNames_Lopn]
          exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨a, ha, hx⟩))
      have hs : ss.map (renOperand τ) = ss := by
        conv_rhs => rw [← List.map_id ss]
        exact List.map_congr_left fun a ha => renOperand_fix fun x hx => h x (by
          rw [defNames_Lopn, useNames_Lopn]
          exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hx⟩))
      simp only [renLinstrR, hd, hs]
  | _ => rfl

/-- **The conditions of the factorization** at an instruction: it mentions no tagged name and
    it is no shadow instruction of a call. -/
structure SortPlain (i : LinstrRM) : Prop where
  /-- No name of the instruction is tagged. -/
  names : ∀ x ∈ defNames i.1 ++ useNames i.1, ¬ IsTag x
  /-- The instruction is no shadow instruction of a call. -/
  noCall : shadowCall? i.1 = none

/-- Every instruction of the code satisfies `SortPlain`. -/
def NoTag (C : List LinstrRM) : Prop := ∀ i ∈ C, SortPlain i

/-- No source of an operation is a compile-time array element `.arr`. -/
def NoArrSrcRM (i : LinstrRM) : Prop :=
  ∀ ds o ss, i.1 = .Lopn ds o ss → ∀ q ∈ ss, ∀ b k, q ≠ LOperand.arr b k

theorem renOpR_comp (σ ρ : String → String) (o : LOperand) :
    X86Backend.ImageCoalesceCfg.renOpR σ (X86Backend.ImageCoalesceCfg.renOpR ρ o)
      = X86Backend.ImageCoalesceCfg.renOpR (σ ∘ ρ) o := by
  cases o <;> rfl

theorem renOpA_comp (σ ρ : String → String) (o : LOperand) :
    renOpA σ (renOpA ρ o) = renOpA (σ ∘ ρ) o := by
  cases o <;> rfl

theorem renLoad_renLoad (σ ρ : String → String) (w : LinstrR) :
    renLoad σ (renLoad ρ w) = renLoad (σ ∘ ρ) w := by
  rcases h : loadStruct? w with _ | ⟨d, b, x⟩
  · rw [X86Backend.ImageCoalesceCfg.renLoad_of_none h, X86Backend.ImageCoalesceCfg.renLoad_of_none h,
      X86Backend.ImageCoalesceCfg.renLoad_of_none h]
  · have hw : ∃ sc, w = .Lopn [.reg d] "LOADIDX" [.arrIdx b x sc] := by
      unfold loadStruct? at h
      split at h
      · split_ifs at h with ho
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        subst ho
        exact ⟨_, rfl⟩
      · cases h
    obtain ⟨sc, rfl⟩ := hw
    simp [renLoad]

theorem renStore_renStore (σ ρ : String → String) (w : LinstrR) :
    renStore σ (renStore ρ w) = renStore (σ ∘ ρ) w := by
  rcases h : storeStruct? w with _ | ⟨d, b, x, v⟩
  · rw [X86Backend.ImageCoalesceCfg.renStore_of_none h,
      X86Backend.ImageCoalesceCfg.renStore_of_none h, X86Backend.ImageCoalesceCfg.renStore_of_none h]
  · have hw : ∃ sc, w = .Lopn [.reg d] "STOREIDX" [.arrIdx b x sc, .reg v] := by
      unfold storeStruct? at h
      split at h
      · split_ifs at h with ho
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        subst ho
        exact ⟨_, rfl⟩
      · cases h
    obtain ⟨sc, rfl⟩ := hw
    simp [renStore]

theorem renZero_renZero (σ ρ : String → String) (w : LinstrR) :
    renZero σ (renZero ρ w) = renZero (σ ∘ ρ) w := by
  rcases h : zeroStruct? w with _ | d
  · rw [X86Backend.ImageCoalesceCfg.renZero_of_none h, X86Backend.ImageCoalesceCfg.renZero_of_none h,
      X86Backend.ImageCoalesceCfg.renZero_of_none h]
  · have hw : ∃ ss, w = .Lopn [.reg d] "ZEROARR" ss := by
      unfold zeroStruct? at h
      split at h
      · split_ifs at h with ho
        simp only [Option.some.injEq] at h
        subst h ho
        exact ⟨_, rfl⟩
      · cases h
    obtain ⟨ss, rfl⟩ := hw
    simp [renZero, List.map_map, Function.comp_def, renOpA_comp]

theorem renStoreImm_renStoreImm (σ ρ : String → String) (w : LinstrR) :
    renStoreImm σ (renStoreImm ρ w) = renStoreImm (σ ∘ ρ) w := by
  rcases h : storeImmStruct? w with _ | ⟨d, b, v, k⟩
  · rw [X86Backend.ImageCoalesceCfg.renStoreImm_of_none h,
      X86Backend.ImageCoalesceCfg.renStoreImm_of_none h,
      X86Backend.ImageCoalesceCfg.renStoreImm_of_none h]
  · have hw : w = .Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k] := by
      unfold storeImmStruct? at h
      split at h
      · split_ifs at h with ho
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        subst ho
        rfl
      · cases h
    subst hw
    simp [renStoreImm]

theorem renCallW_renCallW (σ ρ : String → String) (w : LinstrR) :
    renCallW σ (renCallW ρ w) = renCallW (σ ∘ ρ) w := by
  rcases h : shadowCall? w with _ | ⟨dst, f, srcs⟩
  · rw [renCallW_of_none h, renCallW_of_none h, renCallW_of_none h]
  · rw [eq_callShadow_of_shadowCall? h]
    simp only [X86Backend.ImageCoalesceCfg.renCallW_callShadow, List.map_map, Function.comp_def,
      renOpR_comp]

/-- **The renamings of array positions compose.** -/
theorem renArr_renArr (σ ρ : String → String) (i : LinstrRM) :
    renArr σ (renArr ρ i) = renArr (σ ∘ ρ) i := by
  obtain ⟨w, tag⟩ := i
  cases tag <;> simp only [renArr, renLoad_renLoad, renStore_renStore, renZero_renZero,
    renStoreImm_renStoreImm, renCallW_renCallW]

theorem untag_comp_tagA (σ : String → String) : untag σ ∘ tagA = σ :=
  funext fun x => untag_tagA σ x

/-- **The renaming of the array positions factors through the tagged namespace**: on an
    instruction of `SortPlain` with no compile-time array element among the sources of an
    array zeroing, `renArr σ` is the tagging of the array positions followed by the renaming
    `untag σ` of every name. -/
theorem renArr_factor (σ : String → String) {i : LinstrRM} (h : SortPlain i)
    (hz : ∀ a n, i.2 = .zero a n → NoArrSrcRM i) :
    renRM (untag σ) (renArr tagA i) = renArr σ i := by
  obtain ⟨w, tag⟩ := i
  have hfix : ∀ x ∈ defNames w ++ useNames w, untag σ x = x :=
    fun x hx => untag_of_not (h.names x hx)
  have hid : renLinstrR (untag σ) w = w := renLinstrR_fix hfix
  have hT : ∀ x, untag σ (tagA x) = σ x := untag_tagA σ
  have hcall : shadowCall? w = none := h.noCall
  cases tag with
  | load a n =>
      show (renLinstrR (untag σ) (renLoad tagA w), MemTag.load a n) = (renLoad σ w, _)
      congr 1
      unfold renLoad
      split
      · next d opn b x sc =>
          have hd := hfix d (by simp [opNames])
          have hb := hfix b (by simp [opNames])
          have hx := hfix x (by simp [opNames])
          split_ifs <;> simp [renLinstrR, renOperand, hd, hb, hx, hT]
      · exact hid
  | store a n =>
      show (renLinstrR (untag σ) (renStore tagA w), MemTag.store a n) = (renStore σ w, _)
      congr 1
      unfold renStore
      split
      · next d opn b x sc v =>
          have hd := hfix d (by simp [opNames])
          have hb := hfix b (by simp [opNames])
          have hx := hfix x (by simp [opNames])
          have hv := hfix v (by simp [opNames])
          split_ifs <;> simp [renLinstrR, renOperand, hd, hb, hx, hv, hT]
      · exact hid
  | zero a n =>
      show (renLinstrR (untag σ) (renZero tagA w), MemTag.zero a n) = (renZero σ w, _)
      congr 1
      unfold renZero
      split
      · next d opn ss =>
          have hd := hfix d (by simp [opNames])
          split_ifs
          · simp only [renLinstrR, List.map_cons, List.map_nil, renOperand, hT, List.map_map]
            congr 1
            refine List.map_congr_left fun q hq => ?_
            have hq' := hz a n rfl _ _ _ rfl q hq
            cases q with
            | reg y =>
                have hy := hfix y (by
                  rw [defNames_Lopn, useNames_Lopn]
                  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hq, by simp [opNames]⟩))
                simp [renOpA, renOperand, hy]
            | arr b k => exact absurd rfl (hq' b k)
            | arrIdx b x sc =>
                have hx := hfix x (by
                  rw [defNames_Lopn, useNames_Lopn]
                  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hq, by simp [opNames]⟩))
                simp [renOpA, renOperand, hx, hT]
            | _ => rfl
          · exact hid
      · exact hid
  | storeImm a n =>
      show (renLinstrR (untag σ) (renStoreImm tagA w), MemTag.storeImm a n) =
        (renStoreImm σ w, _)
      congr 1
      unfold renStoreImm
      split
      · next d opn b v k =>
          have hd := hfix d (by simp [opNames])
          have hb := hfix b (by simp [opNames])
          have hv := hfix v (by simp [opNames])
          split_ifs <;> simp [renLinstrR, renOperand, hd, hb, hv, hT]
      · exact hid
  | _ => simp only [renArr, renRM, renCallW_of_none hcall, hid]

/-- A compare (`cmpArgs?`) is its own renaming of array positions. -/
theorem renArr_of_cmp (σ : String → String) {i : LinstrRM}
    (h : (JasminLsemMemFlagGuard.cmpArgs? i).isSome = true) : renArr σ i = i := by
  obtain ⟨w, tag⟩ := i
  have hw : ∃ d a b, w = .Lopn [d] (withWidthTag 64 "CMP") [a, b] := by
    unfold JasminLsemMemFlagGuard.cmpArgs? at h
    split at h
    · split at h
      · next heq ho => subst ho; exact ⟨_, _, _, heq⟩
      · cases h
    · cases h
  obtain ⟨d, a, b, rfl⟩ := hw
  have hs : shadowCall? (.Lopn [d] (withWidthTag 64 "CMP") [a, b]) = none := by
    cases d <;> rfl
  have h1 : withWidthTag 64 "CMP" ≠ "STOREIDX" := by decide
  have h2 : withWidthTag 64 "CMP" ≠ "ZEROARR" := by decide
  have h3 : withWidthTag 64 "CMP" ≠ "LOADIDX" := by decide
  have h4 : withWidthTag 64 "CMP" ≠ "STOREIMM" := by decide
  cases tag <;> simp only [renArr, renCallW_of_none hs] <;>
    first
    | rfl
    | (unfold renLoad; split <;> simp_all)
    | (unfold renStore; split <;> simp_all)
    | (unfold renZero; split <;> simp_all)
    | (unfold renStoreImm; split <;> simp_all)

/-- An instruction whose renaming of array positions is a compare is a compare. -/
theorem isSome_cmpArgs?_of_renArr (σ : String → String) {i : LinstrRM}
    (h : (JasminLsemMemFlagGuard.cmpArgs? (renArr σ i)).isSome = true) :
    (JasminLsemMemFlagGuard.cmpArgs? i).isSome = true := by
  obtain ⟨w, tag⟩ := i
  cases tag <;> simp only [renArr] at h
  all_goals first
    | (unfold renLoad at h; split at h <;> (try split_ifs at h) <;>
        simp_all [JasminLsemMemFlagGuard.cmpArgs?])
    | (unfold renStore at h; split at h <;> (try split_ifs at h) <;>
        simp_all [JasminLsemMemFlagGuard.cmpArgs?])
    | (unfold renZero at h; split at h
       · next d opn ss =>
           split_ifs at h <;> rcases ss with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
             simp_all [JasminLsemMemFlagGuard.cmpArgs?]
       · exact h)
    | (unfold renStoreImm at h; split at h <;> (try split_ifs at h) <;>
        simp_all [JasminLsemMemFlagGuard.cmpArgs?])
    | (unfold renCallW at h; split at h
       · next dst f srcs hs =>
           rw [eq_callShadow_of_shadowCall? hs]
           rcases srcs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
             simp_all [JasminLsemMemFlagGuard.cmpArgs?, LprogIsa.callShadow]
       · exact h)

/-! ## 3. The renaming keeps the control structure -/

/-- The renaming of array positions keeps an instruction, or maps an operation to an
    operation with one register destination. -/
theorem renArr_fst_cases (σ : String → String) (i : LinstrRM) :
    (renArr σ i).1 = i.1 ∨ ((∃ ds o ss, i.1 = .Lopn ds o ss)
      ∧ ∃ x o ss, (renArr σ i).1 = .Lopn [.reg x] o ss) := by
  obtain ⟨w, tag⟩ := i
  cases tag <;> simp only [renArr]
  · unfold renCallW; split
    · next h => right; rw [eq_callShadow_of_shadowCall? h]; exact ⟨⟨_, _, _, rfl⟩, _, _, _, rfl⟩
    · exact Or.inl rfl
  · unfold renLoad; split
    · split_ifs
      · exact Or.inr ⟨⟨_, _, _, rfl⟩, _, _, _, rfl⟩
      · exact Or.inl rfl
    · exact Or.inl rfl
  · unfold renStore; split
    · split_ifs
      · exact Or.inr ⟨⟨_, _, _, rfl⟩, _, _, _, rfl⟩
      · exact Or.inl rfl
    · exact Or.inl rfl
  all_goals first
    | (unfold renZero; split
       · split_ifs
         · exact Or.inr ⟨⟨_, _, _, rfl⟩, _, _, _, rfl⟩
         · exact Or.inl rfl
       · exact Or.inl rfl)
    | (unfold renStoreImm; split
       · split_ifs
         · exact Or.inr ⟨⟨_, _, _, rfl⟩, _, _, _, rfl⟩
         · exact Or.inl rfl
       · exact Or.inl rfl)
    | (unfold renCallW; split
       · next h => right; rw [eq_callShadow_of_shadowCall? h]; exact ⟨⟨_, _, _, rfl⟩, _, _, _, rfl⟩
       · exact Or.inl rfl)

theorem renArr_ctl (σ : String → String) (i : LinstrRM) :
    labelOf? (renArr σ i).1 = labelOf? i.1 ∧ jumpLabel? (renArr σ i).1 = jumpLabel? i.1
      ∧ isGoto (renArr σ i).1 = isGoto i.1 := by
  rcases renArr_fst_cases σ i with h | ⟨⟨ds, o, ss, h1⟩, x, o', ss', h2⟩
  · rw [h]; exact ⟨rfl, rfl, rfl⟩
  · rw [h1, h2]; exact ⟨rfl, rfl, rfl⟩

theorem regShape_renArr (σ : String → String) {i : LinstrRM} (h : RegShape i) :
    RegShape (renArr σ i) := by
  rcases renArr_fst_cases σ i with h' | ⟨-, x, o, ss, h2⟩
  · intro ds o ss hi; rw [h'] at hi; exact h ds o ss hi
  · intro ds o' ss' hi d hd
    rw [h2] at hi
    cases hi
    simp only [List.mem_singleton] at hd
    exact ⟨x, hd⟩

/-- The renaming of array positions keeps the nesting, the absence of unconditional jumps
    and the register destinations. -/
theorem renArr_nest_noGoto_regDsts {C : List LinstrRM} (σ : String → String) (hN : Nest C)
    (hG : NoGoto C) (hR : RegDsts C) :
    Nest (C.map (renArr σ)) ∧ NoGoto (C.map (renArr σ)) ∧ RegDsts (C.map (renArr σ)) := by
  refine ⟨hN.of_embed id (fun a b hab _ => hab.le) (fun x ix hx _ => ?_)
    (fun a b _ _ _ _ _ _ h => h), fun i hi => ?_, fun i hi => ?_⟩
  · rw [List.getElem?_map] at hx
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact ⟨i, hi, (renArr_ctl σ i).1.symm, (renArr_ctl σ i).2.1.symm⟩
  · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    rw [(renArr_ctl σ i').2.2]
    exact hG i' hi'
  · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    exact regShape_renArr σ (hR i' hi')

theorem labelsOf_map_renArr (σ : String → String) (C : List LinstrRM) :
    labelsOf (C.map (renArr σ)) = labelsOf C := by
  unfold labelsOf
  rw [List.filterMap_map]
  exact List.filterMap_congr fun i _ => by simp [(renArr_ctl σ i).1]

theorem targetsOf_map_renArr (σ : String → String) (C : List LinstrRM) :
    targetsOf (C.map (renArr σ)) = targetsOf C := by
  unfold targetsOf
  rw [List.filterMap_map]
  exact List.filterMap_congr fun i _ => by
    simp [← jumpLabel?_eq_jumpTarget?, (renArr_ctl σ i).2.1]

/-- **The names of the renaming of array positions factor through the tagged namespace**: on
    an instruction of `SortPlain`, the names `renArr σ` reads and writes are the images under
    `untag σ` of those of the tagged instruction. -/
theorem names_renArr_factor (σ : String → String) {i : LinstrRM} (h : SortPlain i) :
    useNames (renArr σ i).1 = (useNames (renArr tagA i).1).map (untag σ)
      ∧ defNames (renArr σ i).1 = (defNames (renArr tagA i).1).map (untag σ) := by
  obtain ⟨w, tag⟩ := i
  by_cases ht : ∃ a n, tag = .zero a n
  · obtain ⟨a, n, rfl⟩ := ht
    have hfix : ∀ x ∈ defNames w ++ useNames w, untag σ x = x :=
      fun x hx => untag_of_not (h.names x hx)
    have hmap : ∀ l : List String, (∀ x ∈ l, untag σ x = x) → l.map (untag σ) = l := by
      intro l hl
      conv_rhs => rw [← List.map_id l]
      exact List.map_congr_left hl
    show useNames (renZero σ w) = (useNames (renZero tagA w)).map (untag σ)
      ∧ defNames (renZero σ w) = (defNames (renZero tagA w)).map (untag σ)
    unfold renZero
    split
    · next d opn ss =>
        split_ifs
        · refine ⟨?_, by simp [untag_tagA, opNames]⟩
          simp only [useNames_Lopn, List.flatMap_map, List.map_flatMap]
          refine List.flatMap_congr fun q hq => ?_
          have hq' : ∀ x ∈ opNames q, untag σ x = x := fun x hx => hfix x (by
            rw [defNames_Lopn, useNames_Lopn]
            exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, hx⟩))
          cases q <;> simp_all [renOpA, opNames, untag_tagA]
        · exact ⟨(hmap _ fun x hx => hfix x (List.mem_append_right _ hx)).symm,
            (hmap _ fun x hx => hfix x (List.mem_append_left _ hx)).symm⟩
    · exact ⟨(hmap _ fun x hx => hfix x (List.mem_append_right _ hx)).symm,
        (hmap _ fun x hx => hfix x (List.mem_append_left _ hx)).symm⟩
  · have he := renArr_factor σ h fun a n hz => absurd ⟨a, n, hz⟩ ht
    rw [← he]
    exact ⟨useNames_renLinstrR _ _, defNames_renLinstrR _ _⟩

/-- **The certificate of the renaming of array positions through the sorted namespace.** On
    code `C` of `NoTag`, a certificate `D` of the tagged code `C.map (renArr tagA)` at `E`
    gives, for every renaming `σ`, the certificate `untag σ '' D` of `C.map (renArr σ)` at
    the names `untag σ '' E`. -/
theorem Cert.renArrS {E : String → Prop} {C : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E (C.map (renArr tagA)) D) (hN : NoTag C) (σ : String → String) :
    Cert (img (untag σ) E) (C.map (renArr σ)) (fun k => img (untag σ) (D k)) := by
  have hmap : (C.map (renArr tagA)).map (renArr (untag σ)) = C.map (renArr σ) := by
    rw [List.map_map]
    exact List.map_congr_left fun i _ => by
      simp only [Function.comp_apply, renArr_renArr, untag_comp_tagA]
  have h := hC.map (renArr (untag σ)) (untag σ) (fun i _ => (renArr_ctl _ i).1)
    (fun i _ => (renArr_ctl _ i).2.1) (fun i _ => (renArr_ctl _ i).2.2)
    (fun i' hi' x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hi'
      rw [renArr_renArr, untag_comp_tagA, (names_renArr_factor σ (hN i hi)).1] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact ⟨y, hy, rfl⟩)
    (fun i' hi' y hy => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hi'
      rw [renArr_renArr, untag_comp_tagA, (names_renArr_factor σ (hN i hi)).2]
      exact List.mem_map_of_mem hy)
  rw [hmap] at h
  exact h

/-- A name whose first character is not `@` is untagged. -/
theorem notTag_of_head {x : String} {c : Char} (h : x.toList.head? = some c) (hc : c ≠ '@') :
    ¬ IsTag x := by
  unfold IsTag
  rw [h]
  simpa using hc

theorem notTag_argName (j : Nat) : ¬ IsTag (argName j) :=
  notTag_of_head (c := 'a') (by simp [argName, String.toList_append]) (by decide)

theorem notTag_regName (j : Nat) : ¬ IsTag (regName j) :=
  notTag_of_head (c := 'r') (by simp [regName, String.toList_append]) (by decide)

/-- **The code of `NoTag` from a certificate.** A code without unconditional jumps and shadow
    instructions of calls, with a certificate of definite assignment at untagged names `E`,
    whose written names are untagged, mentions no tagged name. -/
theorem noTag_of_cert {E : String → Prop} {C : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E C D) (hG : NoGoto C) (hE : ∀ x, E x → ¬ IsTag x)
    (hdef : ∀ i ∈ C, ∀ x ∈ defNames i.1, ¬ IsTag x) (hcall : ∀ i ∈ C, NoShadow i) :
    NoTag C := by
  intro i hi
  refine ⟨fun x hx => ?_, hcall i hi⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact hdef i hi x hx
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    have hlt := (List.getElem?_eq_some_iff.mp hk).1
    rcases hC.use k i hk x hx with h | h
    · obtain ⟨ks, hp⟩ := (fwdPath_of_noGoto hG k hlt.le).path
      obtain ⟨j, -, i', hj, hx'⟩ := hC.written hp x h
      exact hdef i' (List.mem_of_getElem? hj) x hx'
    · exact hE x h

/-! ## 4. Instructions that are their own renaming -/

theorem renArr_of_regTag {σ : String → String} {i : LinstrRM} {c : Option Nat}
    (ht : i.2 = .reg c) (hn : NoShadow i) : renArr σ i = i := by
  obtain ⟨w, tag⟩ := i
  simp only at ht
  subst ht
  have hn' : shadowCall? w = none := hn
  simp only [renArr, renCallW_of_none hn']

theorem map_renArr_of_regTag {σ : String → String} {l : List LinstrRM}
    (h : ∀ i ∈ l, (∃ c, i.2 = .reg c) ∧ NoShadow i) : l.map (renArr σ) = l := by
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun i hi =>
    let ⟨⟨_, hc⟩, hn⟩ := h i hi
    renArr_of_regTag hc hn

@[simp] theorem renArr_movI (σ : String → String) (dst : String) (src : LOperand) :
    renArr σ (movI dst src) = movI dst src :=
  renArr_of_regTag rfl (noShadow_movI dst src)

@[simp] theorem renArr_movImmI (σ : String → String) (dst : String) (k : Nat) :
    renArr σ (movImmI dst k) = movImmI dst k :=
  renArr_movI σ dst (.imm k)

@[simp] theorem renArr_labelI (σ : String → String) (l : LLabel) :
    renArr σ (labelI l) = labelI l :=
  renArr_of_regTag rfl (noShadow_labelI l)

theorem map_renArr_movs {α : Type} (σ : String → String) (f : α → String) (g : α → LOperand)
    (l : List α) :
    (l.map fun a => movI (f a) (g a)).map (renArr σ) = l.map fun a => movI (f a) (g a) := by
  simp only [List.map_map, Function.comp_def, renArr_movI]

theorem map_renArr_seedMoves (σ : String → String) (car : List String) (ops : List LOperand) :
    (seedMoves car ops).map (renArr σ) = seedMoves car ops :=
  map_renArr_movs σ _ _ _

theorem map_renArr_parMoves (σ : String → String) (D : Nat) (tgts : List String)
    (ops : List LOperand) :
    (ExportRegions.parMoves D tgts ops).map (renArr σ) = ExportRegions.parMoves D tgts ops := by
  unfold ExportRegions.parMoves stageMoves commitMoves
  rw [List.map_append, map_renArr_movs, map_renArr_movs]

theorem map_renArr_advanceOps (σ : String → String) (idx ctr : String) :
    (advanceOps idx ctr).map (renArr σ) = advanceOps idx ctr :=
  map_renArr_of_regTag fun i hi => ⟨by
    simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact ⟨_, rfl⟩, noShadow_advanceOps idx ctr i hi⟩

theorem map_renArr_flagWord (σ : String → String) (r z : String) (op : LOperand) :
    (flagWord x86Data r z op).map (renArr σ) = flagWord x86Data r z op :=
  map_renArr_of_regTag fun i hi => ⟨by
    unfold flagWord at hi
    split at hi
    · split at hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
      · cases hi
    · rw [List.mem_singleton.mp hi]
      exact ⟨_, rfl⟩, noShadow_flagWord x86Data_guardsNoShadow r z op i hi⟩

theorem map_renArr_zeroTrip (σ : String → String) (c : String) (t e : LLabel) :
    ((x86Data.zeroTripGuard c t e).map guardI).map (renArr σ)
      = (x86Data.zeroTripGuard c t e).map guardI :=
  map_renArr_of_regTag fun i hi => ⟨by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hi
    exact ⟨_, rfl⟩, noShadow_x86Guards.1 c t e i hi⟩

theorem map_renArr_loopGuard (σ : String → String) (c : String) (t : LLabel) :
    ((x86Data.loopGuard c t).map guardI).map (renArr σ) = (x86Data.loopGuard c t).map guardI :=
  map_renArr_of_regTag fun i hi => ⟨by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hi
    exact ⟨_, rfl⟩, noShadow_x86Guards.2 c t i hi⟩

theorem renArr_guardI_cmp (σ : String → String) (c : String) :
    renArr σ (guardI (.Lopn [.reg c] (withWidthTag 64 "CMP") [.reg c, .imm 0]))
      = guardI (.Lopn [.reg c] (withWidthTag 64 "CMP") [.reg c, .imm 0]) :=
  renArr_of_regTag rfl rfl

theorem renArr_guardI_cond (σ : String → String) (c : LOperand) (l : LLabel) :
    renArr σ (guardI (.Lcond c l)) = guardI (.Lcond c l) :=
  renArr_of_regTag rfl rfl

/-! ## 5. The tagged array moves -/

/-- The array move between the tagged names of a move. -/
def tagM (a : ArrMove) : ArrMove := ⟨tagA a.dst, tagA a.src, a.w, a.n⟩

theorem map_renArr_arrMove (z t : String) (a : ArrMove) :
    (arrMove z t a).map (renArr tagA) = arrMove z t (tagM a) := by
  simp [arrMove, renArr, renLoad, renStore, tagM]

theorem map_renArr_arrMoves (z t : String) (mv : List ArrMove) :
    (arrMoves z t mv).map (renArr tagA) = arrMoves z t (mv.map tagM) := by
  simp only [arrMoves, List.map_flatMap, List.flatMap_map, map_renArr_arrMove]

/-! ## 6. Sorted names -/

/-- The name of a binding of type `t` named `x` in the sorted namespace: `x` for a register
    type and `tagA x` for a stack array. -/
def sortName (t : JasminTy) (x : String) : String := if isRegTy t then x else tagA x

theorem sortName_of_reg {t : JasminTy} (h : isRegTy t = true) (x : String) :
    sortName t x = x := by
  simp [sortName, h]

theorem sortName_of_arr {t : JasminTy} (h : isRegTy t = false) (x : String) :
    sortName t x = tagA x := by
  simp [sortName, h]

/-- An argument name of a function of `nArgs` arguments in either namespace. -/
def ArgS (nArgs : Nat) (x : String) : Prop :=
  ∃ j, j < nArgs ∧ (x = argName j ∨ x = tagA (argName j))

/-- The names the tagged code of an export may read without a prior write: the argument
    names in either namespace and the symbol operands of its symbol-base loads. -/
def ExportES (nArgs : Nat) (code : List LinstrRM) (x : String) : Prop :=
  ArgS nArgs x ∨ ∃ i ∈ code, x ∈ symReads i

/-- A binding in scope in the context `Γ` at its sorted name: the binding at the position
    `s`, `nArgs ≤ s < Γ.length`, counted from the root, of type `Γ[Γ.length - 1 - s]`, named
    `regName s`. -/
def InScopeS (nArgs : Nat) (Γ : Ctxt jasminDialect) (x : String) : Prop :=
  ∃ s t, nArgs ≤ s ∧ s < Γ.length ∧ Γ[Γ.length - 1 - s]? = some t ∧ x = sortName t (regName s)

/-- A name of the carried block from `regName D` of the types `cs` at its sorted name: the
    binder `j` of type `cs[j]` named `regName (D + (cs.length - 1 - j))`. -/
def CarS (D : Nat) (cs : List JasminTy) (x : String) : Prop :=
  ∃ j t, cs[j]? = some t ∧ x = sortName t (regName (D + (cs.length - 1 - j)))

/-- The sorted name of a returned register operand of the types `ts` that is no argument
    name. -/
def ResNS (nArgs : Nat) (ts : List JasminTy) (os : List LOperand) (x : String) : Prop :=
  ∃ t y, (t, LOperand.reg y) ∈ ts.zip os ∧ ¬ ArgName nArgs y ∧ x = sortName t y

theorem argS_sortName {nArgs j : Nat} (hj : j < nArgs) (t : JasminTy) :
    ArgS nArgs (sortName t (argName j)) :=
  ⟨j, hj, by unfold sortName; split <;> simp⟩

theorem inScopeS_append {nArgs : Nat} {cs Γ' : Ctxt jasminDialect} {x : String}
    (h : InScopeS nArgs (cs ++ Γ') x) : InScopeS nArgs Γ' x ∨ CarS Γ'.length cs x := by
  obtain ⟨s, t, h1, h2, h3, rfl⟩ := h
  rw [List.length_append] at h2 h3
  by_cases hs : s < Γ'.length
  · left
    refine ⟨s, t, h1, hs, ?_, rfl⟩
    rw [List.getElem?_append_right (by omega)] at h3
    rwa [show cs.length + Γ'.length - 1 - s - cs.length = Γ'.length - 1 - s by omega] at h3
  · right
    rw [List.getElem?_append_left (by omega)] at h3
    exact ⟨_, t, h3, by congr 2; omega⟩

theorem inScopeS_cons {nArgs : Nat} {t : JasminTy} {Γ' : Ctxt jasminDialect} {x : String}
    (h : InScopeS nArgs (t :: Γ') x) :
    InScopeS nArgs Γ' x ∨ x = sortName t (regName Γ'.length) := by
  rcases inScopeS_append (cs := [t]) h with h' | ⟨j, t', hj, rfl⟩
  · exact Or.inl h'
  · right
    cases j with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rfl
    | succ j => simp at hj

/-- The entry of a context at the index of a variable is the type of the variable. -/
theorem getElem?_varIndex {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) :
    Γ[varIndex v]? = some τ := by
  induction v with
  | here => rfl
  | there v ih => simpa [varIndex] using ih

theorem resolveVar_okS {nArgs d : Nat} {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) (hd : Γ.length = d) :
    ∃ y, resolveVar d nArgs argName (fun _ => none) v = .reg y
      ∧ (ArgName nArgs y ∨ InScopeS nArgs Γ (sortName τ y)) := by
  have hv := JasminLsemSimulation.varIndex_lt v
  have hg := getElem?_varIndex v
  unfold resolveVar
  dsimp only
  split
  · exact ⟨_, rfl, Or.inl ⟨_, by assumption, rfl⟩⟩
  · refine ⟨_, rfl, Or.inr ⟨d - 1 - varIndex v, τ, by omega, by omega, ?_, rfl⟩⟩
    rw [show Γ.length - 1 - (d - 1 - varIndex v) = varIndex v by omega]
    exact hg

theorem exprArgsHV_okS {nArgs d : Nat} {Γ : Ctxt jasminDialect} (hd : Γ.length = d) :
    ∀ {ts : List JasminTy} (vs : HVector (fun t => Ctxt.Var Γ t) ts),
      ∀ p ∈ ts.zip (exprArgsHV d nArgs argName (fun _ => none) vs),
        ∃ y, p.2 = .reg y ∧ (ArgName nArgs y ∨ InScopeS nArgs Γ (sortName p.1 y))
  | [], .nil => by simp [exprArgsHV]
  | _ :: _, .cons v rest => by
      intro p hp
      rw [show exprArgsHV d nArgs argName (fun _ => none) (.cons v rest)
        = resolveVar d nArgs argName (fun _ => none) v
          :: exprArgsHV d nArgs argName (fun _ => none) rest from rfl, List.zip_cons_cons,
        List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact resolveVar_okS v hd
      · exact exprArgsHV_okS hd rest p hp

theorem exprArgsHV_memS {nArgs d : Nat} {Γ : Ctxt jasminDialect} (hd : Γ.length = d) :
    ∀ {ts : List JasminTy} (vs : HVector (fun t => Ctxt.Var Γ t) ts),
      ∀ o ∈ exprArgsHV d nArgs argName (fun _ => none) vs,
        ∃ τ ∈ ts, ∃ y, o = .reg y ∧ (ArgName nArgs y ∨ InScopeS nArgs Γ (sortName τ y))
  | [], .nil => by simp [exprArgsHV]
  | _ :: _, .cons v rest => by
      intro o ho
      rw [show exprArgsHV d nArgs argName (fun _ => none) (.cons v rest)
        = resolveVar d nArgs argName (fun _ => none) v
          :: exprArgsHV d nArgs argName (fun _ => none) rest from rfl, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact ⟨_, List.mem_cons_self, resolveVar_okS v hd⟩
      · obtain ⟨τ, hτ, h⟩ := exprArgsHV_memS hd rest o ho
        exact ⟨τ, List.mem_cons_of_mem _ hτ, h⟩

theorem exprArgs_go_memS {nArgs d : Nat} {Γ : Ctxt jasminDialect} (hd : Γ.length = d) :
    ∀ {ts : List JasminTy} (vs : HVector (fun t => Ctxt.Var Γ t) ts),
      ∀ o ∈ exprArgs.go d nArgs argName (fun _ => none) vs,
        ∃ τ ∈ ts, ∃ y, o = .reg y ∧ (ArgName nArgs y ∨ InScopeS nArgs Γ (sortName τ y))
  | [], .nil => by simp [exprArgs.go]
  | _ :: _, .cons v rest => by
      intro o ho
      rw [show exprArgs.go d nArgs argName (fun _ => none) (.cons v rest)
        = resolveVar d nArgs argName (fun _ => none) v
          :: exprArgs.go d nArgs argName (fun _ => none) rest from rfl, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact ⟨_, List.mem_cons_self, resolveVar_okS v hd⟩
      · obtain ⟨τ, hτ, h⟩ := exprArgs_go_memS hd rest o ho
        exact ⟨τ, List.mem_cons_of_mem _ hτ, h⟩

/-- A sorted name of an argument or of a binding in scope is in `X` or `E`. -/
theorem good_of_okS {nArgs : Nat} {Γ : Ctxt jasminDialect} {E X : String → Prop}
    (hE : ∀ x, ArgS nArgs x → E x) (hX : ∀ x, InScopeS nArgs Γ x → X x) {t : JasminTy}
    {y : String} (h : ArgName nArgs y ∨ InScopeS nArgs Γ (sortName t y)) :
    X (sortName t y) ∨ E (sortName t y) := by
  rcases h with ⟨j, hj, rfl⟩ | h
  · exact Or.inr (hE _ (argS_sortName hj t))
  · exact Or.inl (hX _ h)

/-- The sorted name of a returned register operand is an argument name or of `ResNS`. -/
theorem goodRes {nArgs : Nat} {ts : List JasminTy} {os : List LOperand} {E : String → Prop}
    (hE : ∀ x, ArgS nArgs x → E x) (hreg : ∀ o ∈ os, o = .reg (operandName o)) :
    ∀ p ∈ ts.zip os, ResNS nArgs ts os (sortName p.1 (operandName p.2))
      ∨ E (sortName p.1 (operandName p.2)) := by
  intro p hp
  have hy := hreg p.2 (List.of_mem_zip hp).2
  by_cases ha : ArgName nArgs (operandName p.2)
  · obtain ⟨j, hj, he⟩ := ha
    rw [he]
    exact Or.inr (hE _ (argS_sortName hj _))
  · exact Or.inl ⟨p.1, operandName p.2, by rw [← hy]; exact hp, ha, rfl⟩

theorem mem_zip_of_mem_right {α β : Type} {l₁ : List α} {l₂ : List β} {b : β} (hb : b ∈ l₂)
    (hlen : l₁.length = l₂.length) : ∃ a, (a, b) ∈ l₁.zip l₂ := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  exact ⟨l₁[j]'(by omega), List.mem_iff_getElem.mpr ⟨j, by simp; omega, by simp⟩⟩

/-! ## 7. The typed pairs -/

theorem carriedPairs_srcS {cs : List JasminTy} {car : List String} {ops : List LOperand}
    {p : JasminTy × String × String} (hp : p ∈ carriedPairs cs car ops) :
    ∃ o, (p.1, o) ∈ cs.zip ops ∧ p.2.2 = operandName o := by
  unfold carriedPairs at hp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
  simp only [List.length_zip, List.length_map] at hj
  refine ⟨ops[j]'(by omega), List.mem_iff_getElem.mpr ⟨j, by simp; omega, ?_⟩, by simp⟩
  simp

theorem carriedPairs_tgtS {D : Nat} {cs : List JasminTy} {ops : List LOperand}
    (hlen : cs.length ≤ ops.length) :
    ∀ x, CarS D cs x → ∃ p ∈ carriedPairs cs (carriedRegs D cs.length) ops,
      x = sortName p.1 p.2.1 := by
  rintro x ⟨j, t, hj, rfl⟩
  have hjl := (List.getElem?_eq_some_iff.mp hj).1
  have hjt := (List.getElem?_eq_some_iff.mp hj).2
  refine ⟨(t, regName (D + (cs.length - 1 - j)), operandName (ops[j]'(by omega))),
    List.mem_iff_getElem.mpr ⟨j, by simp [carriedPairs, carriedRegs]; omega, ?_⟩, rfl⟩
  simp [carriedPairs, carriedRegs, hjt]

/-- A typed pair of the carried block from `regName D` read as register operands names a
    binder of the block at its sorted name. -/
theorem carS_of_zip {D : Nat} {cs : List JasminTy} {q : JasminTy × LOperand}
    (hq : q ∈ cs.zip ((carriedRegs D cs.length).map LOperand.reg)) :
    CarS D cs (sortName q.1 (operandName q.2)) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
  simp only [List.length_zip, List.length_map, carriedRegs, List.length_range] at hj
  exact ⟨j, cs[j]'(by omega), by simp, by simp [carriedRegs, operandName]⟩

theorem shiftPairs_eq (d : Nat) (cs : List JasminTy) :
    shiftPairs d cs = (carriedPairs cs (carriedRegs d cs.length)
      ((carriedRegs (d + 1) cs.length).map LOperand.reg)).reverse := by
  simp [shiftPairs, carriedPairs, List.map_map, Function.comp_def, operandName]

theorem mem_arrPairsS {tp : List (JasminTy × String × String)} {a : ArrMove}
    (h : a ∈ arrPairs tp) : ∃ p ∈ tp, isRegTy p.1 = false ∧ a.dst = p.2.1 ∧ a.src = p.2.2 := by
  obtain ⟨p, hp, hq⟩ := List.mem_filterMap.mp h
  rcases p with ⟨ty, x, y⟩
  cases ty <;> simp at hq
  subst hq
  exact ⟨_, hp, rfl, rfl, rfl⟩

theorem mem_regPairsS {tp : List (JasminTy × String × String)} {q : String × String}
    (h : q ∈ regPairs tp) : ∃ p ∈ tp, isRegTy p.1 = true ∧ q = p.2 := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact ⟨p, (List.mem_filter.mp hp).1, (List.mem_filter.mp hp).2, rfl⟩

/-- Every typed pair is an array pair whose tagged target is its sorted target, or a register
    pair whose target is its sorted target. -/
theorem pair_coverS {tp : List (JasminTy × String × String)} {p : JasminTy × String × String}
    (hp : p ∈ tp) : (∃ a ∈ arrPairs tp, tagA a.dst = sortName p.1 p.2.1)
      ∨ (∃ q ∈ regPairs tp, q.1 = sortName p.1 p.2.1) := by
  rcases p with ⟨ty, x, y⟩
  cases ty with
  | stackArr w n =>
      exact Or.inl ⟨⟨x, y, w, n⟩, List.mem_filterMap.mpr ⟨_, hp, rfl⟩, rfl⟩
  | _ => exact Or.inr ⟨(x, y), List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩, rfl⟩

/-! ## 8. Blocks of the tagged frame instructions -/

variable {E : String → Prop} {Λ : LLabel → String → Prop}

theorem blk_cons2 {X Y Z : String → Prop} {a b : LinstrRM} {c : List LinstrRM}
    (h₁ : Blk E Λ X [a, b] Y) (h₂ : Blk E Λ Y c Z) : Blk E Λ X (a :: b :: c) Z :=
  Blk.append h₁ h₂

/-- The block of the tagged array moves `mv`. -/
theorem blk_arrMovesS (z t : String) (mv : List ArrMove) {X : String → Prop} (hz : X z)
    (hs : ∀ a ∈ mv, X (tagA a.src) ∨ E (tagA a.src)) :
    Blk E Λ X ((arrMoves z t mv).map (renArr tagA)) (fun r => X r ∨ ∃ a ∈ mv, r = tagA a.dst) := by
  rw [map_renArr_arrMoves]
  refine (blk_arrMoves z t (mv.map tagM) hz fun a ha => ?_).mono (fun _ h => h) fun r hr => ?_
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact hs b hb
  · rcases hr with h | ⟨a, ha, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨tagM a, List.mem_map_of_mem ha, rfl⟩

/-- The block of the tagged typed moves: it is followed by the names of `X` and the sorted
    targets. -/
theorem blk_typedMovesS (z t : String) (tp : List (JasminTy × String × String))
    {X : String → Prop} (hz : X z) (hs : ∀ p ∈ tp, X (sortName p.1 p.2.2) ∨ E (sortName p.1 p.2.2)) :
    Blk E Λ X ((typedMoves z t tp).map (renArr tagA))
      (fun r => X r ∨ ∃ p ∈ tp, r = sortName p.1 p.2.1) := by
  unfold typedMoves regMoves
  rw [List.map_append, map_renArr_movs]
  refine Blk.append (blk_arrMovesS z t (arrPairs tp) hz fun a ha => ?_)
    ((blk_movs (fun q => q.1) (fun q => .reg q.2) (regPairs tp) fun q hq x hx => ?_).mono
      (fun _ h => h) fun r hr => ?_)
  · obtain ⟨p, hp, hr, -, he⟩ := mem_arrPairsS ha
    rw [he, ← sortName_of_arr hr]
    exact hs p hp
  · obtain ⟨p, hp, hr, rfl⟩ := mem_regPairsS hq
    simp only [opNames, List.mem_singleton] at hx
    subst hx
    rcases hs p hp with h | h
    · exact Or.inl (Or.inl (by rwa [sortName_of_reg hr] at h))
    · exact Or.inr (by rwa [sortName_of_reg hr] at h)
  · rcases hr with h | ⟨p, hp, rfl⟩
    · exact Or.inl (Or.inl h)
    · rcases pair_coverS hp with ⟨a, ha, he⟩ | ⟨q, hq, he⟩
      · exact Or.inl (Or.inr ⟨a, ha, he.symm⟩)
      · exact Or.inr ⟨q, hq, he.symm⟩

/-- The block of a tagged parallel assignment of arrays: it is followed by the names of `X`
    and the tagged targets. -/
theorem blk_arrParMovesS (z t : String) (D : Nat) (mv : List ArrMove) {X : String → Prop}
    (hz : X z) (hs : ∀ a ∈ mv, X (tagA a.src) ∨ E (tagA a.src)) :
    Blk E Λ X ((arrParMoves z t D mv).map (renArr tagA))
      (fun r => X r ∨ ∃ a ∈ mv, r = tagA a.dst) := by
  unfold arrParMoves
  split
  · exact blk_arrMovesS z t mv hz hs
  · rw [List.map_append]
    refine Blk.append (blk_arrMovesS z t (arrStage D mv) hz fun a ha => ?_) ?_
    · obtain ⟨b, hb, he⟩ := mem_arrStage_src ha
      rw [he]
      exact hs b hb
    · refine (blk_arrMovesS z t (arrCommit D mv) (Or.inl hz) fun a ha => ?_).mono
        (fun _ h => h) fun r hr => ?_
      · obtain ⟨b, hb, he⟩ := mem_arrCommit_src ha
        exact Or.inl (Or.inr ⟨b, hb, by rw [he]⟩)
      · rcases hr with h | ⟨b, hb, rfl⟩
        · exact Or.inl (Or.inl h)
        · obtain ⟨a, ha, he⟩ := mem_arrCommit_dst (D := D) hb
          exact Or.inr ⟨a, ha, by rw [he]⟩

/-- The block of the tagged assignment of the results of a branch to the block
    `carriedRegs d rs.length`: it is followed by the names of `X` and the sorted names of
    that block. -/
theorem blk_ifResMovesS (rs : List JasminTy) (d D : Nat) (ops : List LOperand)
    {X : String → Prop}
    (hs : ∀ q ∈ rs.zip ops, X (sortName q.1 (operandName q.2)) ∨ E (sortName q.1 (operandName q.2)))
    (hlen : rs.length ≤ ops.length) :
    Blk E Λ X ((ifResMoves rs d D ops).map (renArr tagA)) (fun r => X r ∨ CarS d rs r) := by
  have hsrc : ∀ p ∈ ifResPairs rs d ops, X (sortName p.1 p.2.2) ∨ E (sortName p.1 p.2.2) := by
    intro p hp
    obtain ⟨o, ho, he⟩ := carriedPairs_srcS hp
    rw [he]
    exact hs _ ho
  have hpar : ∀ {X' : String → Prop}, (∀ x, X x → X' x) →
      Blk E Λ X' (ExportRegions.parMoves D ((regPairs (ifResPairs rs d ops)).map Prod.fst)
        ((regPairs (ifResPairs rs d ops)).map fun p => .reg p.2))
        (fun r => X' r ∨ r ∈ (regPairs (ifResPairs rs d ops)).map Prod.fst) := by
    intro X' hX'
    refine blk_parMoves D _ _ (fun o ho => ?_) (fun o ho => ?_) (by simp)
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ho
      rfl
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
      obtain ⟨p, hp, hr, rfl⟩ := mem_regPairsS hq
      rcases hsrc p hp with h | h
      · exact Or.inl (hX' _ (by rwa [sortName_of_reg hr] at h))
      · exact Or.inr (by rwa [sortName_of_reg hr] at h)
  have htgt : ∀ x, CarS d rs x → ∃ p ∈ ifResPairs rs d ops, x = sortName p.1 p.2.1 :=
    carriedPairs_tgtS hlen
  unfold ifResMoves
  rw [List.map_append, map_renArr_parMoves]
  split
  · next he =>
      refine (hpar (fun _ h => h)).mono (fun _ h => h) fun r hr => ?_
      rcases hr with h | hr
      · exact Or.inl h
      · obtain ⟨p, hp, rfl⟩ := htgt r hr
        rcases pair_coverS hp with ⟨a, ha, -⟩ | ⟨q, hq, he'⟩
        · rw [List.isEmpty_iff.mp he] at ha
          simp at ha
        · exact Or.inr (List.mem_map.mpr ⟨q, hq, he'⟩)
  · rw [List.map_cons, renArr_movImmI]
    refine Blk.append (Blk.cons (blk_movI (regName (D + 1)) (.imm 0) (by simp [opNames]))
      (blk_arrParMovesS _ _ D _ (Or.inr rfl) fun a ha => ?_)) ?_
    · obtain ⟨p, hp, hr, -, he⟩ := mem_arrPairsS ha
      rw [he, ← sortName_of_arr hr]
      rcases hsrc p hp with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · refine (hpar fun _ h => Or.inl (Or.inl h)).mono (fun _ h => h) fun r hr => ?_
      rcases hr with h | hr
      · exact Or.inl (Or.inl (Or.inl h))
      · obtain ⟨p, hp, rfl⟩ := htgt r hr
        rcases pair_coverS hp with ⟨a, ha, he'⟩ | ⟨q, hq, he'⟩
        · exact Or.inl (Or.inr ⟨a, ha, he'.symm⟩)
        · exact Or.inr (List.mem_map.mpr ⟨q, hq, he'⟩)

/-! ## 9. The tagged binding -/

/-- A sorted name of an argument or of a binding in scope in `Γ`. -/
def GoodS (nArgs : Nat) (Γ : Ctxt jasminDialect) (x : String) : Prop :=
  ∃ τ y, x = sortName τ y ∧ (ArgName nArgs y ∨ InScopeS nArgs Γ (sortName τ y))

theorem good_of_goodS {nArgs : Nat} {Γ : Ctxt jasminDialect} {X : String → Prop}
    (hE : ∀ x, ArgS nArgs x → E x) (hX : ∀ x, InScopeS nArgs Γ x → X x) {x : String}
    (h : GoodS nArgs Γ x) : X x ∨ E x := by
  obtain ⟨τ, y, rfl, h⟩ := h
  exact good_of_okS hE hX h

theorem bindOps_sortS_reg (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (hop : opMemB e.op = true) (d : Nat) (hd : Γ.length = d)
    (htag : ∀ i ∈ bindOps nArgs e d, ∃ c, i.2 = .reg c) (hret : isRegTy t = true)
    (hsig : ∀ τ ∈ DialectSignature.sig e.op, isRegTy τ = true) :
    ∃ o ss tag, (bindOps nArgs e d).map (renArr tagA)
        = [(.Lopn [.reg (sortName t (regName d))] o ss, tag)]
      ∧ ∀ x ∈ ss.flatMap opNames, GoodS nArgs Γ x ∨ o = "LOADSYM" := by
  obtain ⟨o, ss, tag, hb, hss⟩ := bindOps_shape nArgs e d
  refine ⟨o, ss, tag, ?_, fun x hx => ?_⟩
  · rw [map_renArr_of_regTag (fun i hi => ⟨htag i hi, noShadow_bindOps nArgs e hop d i hi⟩), hb,
      sortName_of_reg hret]
  · rcases hss x hx with hx' | ho
    · left
      obtain ⟨q, hq, hxq⟩ := List.mem_flatMap.mp hx'
      obtain ⟨τ, hτ, y, rfl, hok⟩ := exprArgs_go_memS hd e.args q hq
      simp only [opNames, List.mem_singleton] at hxq
      subst hxq
      exact ⟨τ, x, (sortName_of_reg (hsig τ hτ) x).symm, hok⟩
    · exact Or.inr ho

/-- **The tagged instruction of a binding** at depth `d = Γ.length` of an operation of
    `opMemB`: an operation writing the sorted name of `regName d` whose read names are sorted
    names of arguments or bindings in scope, or the symbol of a symbol-base load. -/
theorem bindOps_sortS (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (hop : opMemB e.op = true) (d : Nat) (hd : Γ.length = d) :
    ∃ o ss tag, (bindOps nArgs e d).map (renArr tagA)
        = [(.Lopn [.reg (sortName t (regName d))] o ss, tag)]
      ∧ ∀ x ∈ ss.flatMap opNames, GoodS nArgs Γ x ∨ o = "LOADSYM" := by
  obtain ⟨op, heq, args⟩ := e
  cases op <;> simp only [opMemB, Bool.false_eq_true] at hop
  all_goals subst heq
  case stackLoad w n =>
    match args with
    | .cons a (.cons ix .nil) =>
      obtain ⟨b, hb, hokb⟩ := resolveVar_okS (nArgs := nArgs) a hd
      obtain ⟨x, hx, hokx⟩ := resolveVar_okS (nArgs := nArgs) ix hd
      have hs : exprArgs.go d nArgs argName (fun _ => none) (.cons a (.cons ix .nil))
          = [.reg b, .reg x] := by
        show [_, _] = _
        rw [hb, hx]
      refine ⟨"LOADIDX", [.arrIdx (tagA b) x (w / 8)], .load w n, ?_, ?_⟩
      · simp [bindOps, straightOpsMem, exprArgs, hs, opToLinstrR, renArr,
          renLoad, sortName, isRegTy, DialectSignature.ret]
      · intro z hz
        simp only [List.flatMap_cons, List.flatMap_nil, opNames, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with h | h <;> rw [h]
        · exact Or.inl ⟨.stackArr w n, b, (sortName_of_arr rfl b).symm, hokb⟩
        · exact Or.inl ⟨.reg 64, x, (sortName_of_reg rfl x).symm, hokx⟩
  case stackStore w n =>
    match args with
    | .cons a (.cons ix (.cons v .nil)) =>
      obtain ⟨b, hb, hokb⟩ := resolveVar_okS (nArgs := nArgs) a hd
      obtain ⟨x, hx, hokx⟩ := resolveVar_okS (nArgs := nArgs) ix hd
      obtain ⟨y, hy, hoky⟩ := resolveVar_okS (nArgs := nArgs) v hd
      have hs : exprArgs.go d nArgs argName (fun _ => none) (.cons a (.cons ix (.cons v .nil)))
          = [.reg b, .reg x, .reg y] := by
        show [_, _, _] = _
        rw [hb, hx, hy]
      refine ⟨"STOREIDX", [.arrIdx (tagA b) x (w / 8), .reg y], .store w n, ?_, ?_⟩
      · simp [bindOps, straightOpsMem, exprArgs, hs, opToLinstrR, renArr,
          renStore, sortName, isRegTy, DialectSignature.ret]
      · intro z hz
        simp only [List.flatMap_cons, List.flatMap_nil, opNames, List.append_nil,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with h | h | h <;> rw [h]
        · exact Or.inl ⟨.stackArr w n, b, (sortName_of_arr rfl b).symm, hokb⟩
        · exact Or.inl ⟨.reg 64, x, (sortName_of_reg rfl x).symm, hokx⟩
        · exact Or.inl ⟨.reg w, y, (sortName_of_reg rfl y).symm, hoky⟩
  case stackZero w n =>
    refine ⟨"ZEROARR", [.imm n, .imm w], .zero w n, ?_, ?_⟩
    · simp [bindOps, straightOpsMem, opToLinstrR, renArr, renZero, renOpA, sortName, isRegTy,
        DialectSignature.ret]
    · intro z hz
      simp [opNames] at hz
  case stackStoreImm w n i =>
    match args with
    | .cons a (.cons v .nil) =>
      obtain ⟨b, hb, hokb⟩ := resolveVar_okS (nArgs := nArgs) a hd
      obtain ⟨y, hy, hoky⟩ := resolveVar_okS (nArgs := nArgs) v hd
      have hs : exprArgs.go d nArgs argName (fun _ => none) (.cons a (.cons v .nil))
          = [.reg b, .reg y] := by
        show [_, _] = _
        rw [hb, hy]
      refine ⟨"STOREIMM", [.reg (tagA b), .reg y, .imm i], .storeImm w n, ?_, ?_⟩
      · simp [bindOps, straightOpsMem, exprArgs, hs, opToLinstrR, renArr,
          renStoreImm, sortName, isRegTy, DialectSignature.ret]
      · intro z hz
        simp only [List.flatMap_cons, List.flatMap_nil, opNames, List.append_nil,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with h | h <;> rw [h]
        · exact Or.inl ⟨.stackArr w n, b, (sortName_of_arr rfl b).symm, hokb⟩
        · exact Or.inl ⟨.reg w, y, (sortName_of_reg rfl y).symm, hoky⟩
  all_goals
    refine bindOps_sortS_reg nArgs _ (by simp_all [opMemB]) d hd (fun i hi => ?_) rfl
      (fun τ hτ => ?_)
    · simp only [bindOps, straightOpsMem, List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi
      exact ⟨_, rfl⟩
    · revert hτ
      simp only [DialectSignature.sig, List.mem_cons, List.not_mem_nil, or_false]
      first
      | (rintro rfl; rfl)
      | (rintro (rfl | rfl) <;> rfl)
      | (rintro (rfl | rfl | rfl) <;> rfl)

/-! ## 10. The block judgement of the tagged export -/

theorem mem_map_renArr_of_mem {C C' : List LinstrRM} (h : ∀ i ∈ C, i ∈ C') :
    ∀ i ∈ C.map (renArr tagA), i ∈ C'.map (renArr tagA) := by
  intro i hi
  obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
  exact List.mem_map_of_mem (h i' hi')

/-- The block judgement of a tagged export at a label table agreeing with `Λ'` on the
    interval of the labels of the export. -/
theorem blk_congr_labelsOK {Λ': LLabel → String → Prop} {X Y : String → Prop} {n : Nat}
    {r : Exported} (h : Blk E Λ' X (r.code.map (renArr tagA)) Y) (hL : LabelsOK n r)
    (hΛ : ∀ l, n ≤ l → l < r.next → Λ l = Λ' l) : Blk E Λ X (r.code.map (renArr tagA)) Y :=
  h.congr_range (by rw [labelsOf_map_renArr]; exact hL.range)
    (by rw [labelsOf_map_renArr, targetsOf_map_renArr]; exact hL.closed) hΛ

/-- **The block judgement of the tagged export.** For an export `r` of a program over a
    context `Γ` of length `d` whose bindings are in `opMemB` and which has no call, for every
    set `E` containing the argument names in both namespaces and the symbol operands of the
    tagged code, and every set `X` containing the bindings in scope at their sorted names,
    the tagged code has a block certificate from `X` to the names of `X` and the sorted names
    of the returned operands that are no argument names, at some label table. -/
theorem exportR_blkS (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r → Γ.length = d →
      ∀ (E : String → Prop), (∀ x, ArgS nArgs x → E x) → SymOK E (r.code.map (renArr tagA)) →
        ∀ (X : String → Prop), (∀ x, InScopeS nArgs Γ x → X x) →
          ∃ Λ : LLabel → String → Prop,
            Blk E Λ X (r.code.map (renArr tagA)) (fun x => X x ∨ ResNS nArgs ts r.res x) := by
  induction p with
  | ret vs =>
      intro d n r h hd E hE hS X hX
      simp only [exportR, Option.some.injEq] at h
      subst h
      refine ⟨fun _ _ => False, blk_nil fun x hx => ?_⟩
      rcases hx with hx | ⟨t, y, hm, hna, rfl⟩
      · exact hx
      · obtain ⟨y', hy', hok⟩ := exprArgsHV_okS hd vs _ hm
        simp only [LOperand.reg.injEq] at hy'
        subst hy'
        rcases hok with h' | h'
        · exact absurd h' hna
        · exact hX _ h'
  | @var Γ t ts e k ih =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree] at hc
      intro d n r h hd E hE hS X hX
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      obtain ⟨o, ss, tag, hb, hss⟩ := bindOps_sortS nArgs e hp.1 d hd
      simp only [Exported.prepend, List.map_append] at hS ⊢
      rw [hb] at hS ⊢
      have hS' := SymOK.append (a := [_]) hS
      have hX1 : ∀ x, InScopeS nArgs (t :: Γ) x → X x ∨ x = sortName t (regName d) := by
        intro x hx
        rcases inScopeS_cons hx with h' | h'
        · exact Or.inl (hX _ h')
        · exact Or.inr (hd ▸ h')
      obtain ⟨Λ, hB⟩ := ih hp.2 hc _ _ rk hk (by simp [hd]) E hE hS'.2 _ hX1
      refine ⟨Λ, Blk.cons ((blk_opn _ _ _ _ fun x hx => ?_).mono (fun _ h => h) fun x hx => ?_)
        (hB.mono (fun _ h => h) fun x hx => ?_)⟩
      · rcases hss x hx with hg | ho
        · exact good_of_goodS hE hX hg
        · exact Or.inr (hS'.1 _ List.mem_cons_self x (by simp [symReads, ho, hx]))
      · rcases hx with h' | rfl
        · exact Or.inl h'
        · exact Or.inr (by simp [opNames])
      · rcases hx with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
  | call f args k ih =>
      simp [NFProg.callFree] at hc
  | @forLoop Γ cs ts count inits body k ihb ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h hd E hE hS X hX
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      simp only [Exported.prepend, List.map_append] at hS ⊢
      have hSF := SymOK.append hS
      have hLb := exportR_labelsOK nArgs fn x86Data_guardsPlain body _ _ b hb
      have hLk := exportR_labelsOK nArgs fn x86Data_guardsPlain k _ _ rk hk
      have hlenB := exportR_res_length nArgs fn body _ _ b hb
      have hregB := exportR_res_isReg nArgs fn body _ _ b hb
      have hlenI := exprArgsHV_length d nArgs inits
      obtain ⟨cx, hcx, hcxok⟩ := resolveVar_okS (nArgs := nArgs) count hd
      let LN : String → Prop := fun x =>
        X x ∨ x = regName d ∨ x = loopCtr n ∨ CarS (d + 1) cs x
      let KN : String → Prop := fun x => X x ∨ CarS d cs x
      have hLNin : ∀ x, InScopeS nArgs (cs ++ HasWord64.word (d := jasminDialect) :: Γ) x →
          LN x := by
        intro x hx
        rcases inScopeS_append hx with h' | h'
        · rcases inScopeS_cons h' with h'' | h''
          · exact Or.inl (hX _ h'')
          · exact Or.inr (Or.inl (by rw [h'', hd]; rfl))
        · refine Or.inr (Or.inr (Or.inr ?_))
          have : (HasWord64.word (d := jasminDialect) :: Γ).length = d + 1 := by simp [hd]
          rwa [this] at h'
      have hKNin : ∀ x, InScopeS nArgs (cs ++ Γ) x → KN x := by
        intro x hx
        rcases inScopeS_append hx with h' | h'
        · exact Or.inl (hX _ h')
        · exact Or.inr (hd ▸ h')
      have hSb : SymOK E (b.code.map (renArr tagA)) := fun i hi => hSF.1 i
        (mem_map_renArr_of_mem (fun j hj => by unfold forArrFrame; simp [hj]) i hi)
      obtain ⟨Λb, hBb⟩ := ihb hp.1 hc.1 _ _ b hb (by simp [hd]; omega) E hE hSb LN hLNin
      obtain ⟨Λk, hKk⟩ := ihk hp.2 hc.2 _ _ rk hk (by simp [hd]; omega) E hE hSF.2 KN hKNin
      let Λ : LLabel → String → Prop := fun l =>
        if l = n ∨ l = n + 1 then LN else if l < b.next then Λb l else Λk l
      have hΛn : ∀ x, Λ n x = LN x := fun x => by simp [Λ]
      have hΛn1 : ∀ x, Λ (n + 1) x = LN x := fun x => by simp [Λ]
      have hBb' : Blk E Λ LN (b.code.map (renArr tagA))
          (fun x => LN x ∨ ResNS nArgs cs b.res x) :=
        blk_congr_labelsOK hBb hLb fun l h1 h2 => by
          simp only [Λ, ite_eq_right (show ¬(l = n ∨ l = n + 1) by omega), ite_eq_left h2]
      have hKk' : Blk E Λ KN (rk.code.map (renArr tagA))
          (fun x => KN x ∨ ResNS nArgs ts rk.res x) :=
        blk_congr_labelsOK hKk hLk fun l h1 h2 => by
          have := hLb.le
          simp only [Λ, ite_eq_right (show ¬(l = n ∨ l = n + 1) by omega),
            ite_eq_right (show ¬(l < b.next) by omega)]
      have hgoodB := goodRes (nArgs := nArgs) (ts := cs) (E := E) hE hregB
      have hF : Blk E Λ X ((forArrFrame d n cs (exprArgsHV d nArgs argName (fun _ => none) inits)
          (resolveVar d nArgs argName (fun _ => none) count) b.code b.res b.depth
          x86Data).map (renArr tagA)) KN := by
        unfold forArrFrame
        dsimp only
        rw [x86_zeroTrip (loopCtr n) n (n + 1), x86_loopGuard (loopCtr n) n, hcx]
        simp only [List.map_cons, List.map_append, renArr_movImmI, renArr_labelI,
          map_renArr_seedMoves, renArr_guardI_cmp, renArr_guardI_cond, map_renArr_parMoves,
          map_renArr_advanceOps, List.cons_append, List.nil_append]
        -- the seeds
        refine Blk.cons (blk_movI _ _ (by simp [opNames])) ?_
        refine Blk.append (blk_typedMovesS (regName d) _ _ (Or.inr rfl) fun p hp => ?_) ?_
        · obtain ⟨o, ho, he⟩ := carriedPairs_srcS hp
          obtain ⟨y, hy, hok⟩ := exprArgsHV_okS hd inits _ ho
          simp only at hy
          subst hy
          rw [he]
          rcases good_of_okS hE hX hok with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr h'
        refine Blk.append (blk_seed1 (loopCtr n) (.reg cx) fun x hx => ?_) ?_
        · simp only [opNames, List.mem_singleton] at hx
          subst hx
          rcases hcxok with h' | h'
          · exact Or.inr (hE _ ⟨_, h'.choose_spec.1, Or.inl h'.choose_spec.2⟩)
          · rw [sortName_of_reg rfl] at h'
            exact Or.inl (Or.inl (Or.inl (hX _ h')))
        have hLN0 : ∀ x, LN x → (((X x ∨ x = regName d) ∨ ∃ p ∈ carriedPairs cs
            (carriedRegs (d + 1) cs.length) (exprArgsHV d nArgs argName (fun _ => none) inits),
              x = sortName p.1 p.2.1) ∨ x = loopCtr n) := by
          rintro x (h' | rfl | rfl | h')
          · exact Or.inl (Or.inl (Or.inl h'))
          · exact Or.inl (Or.inl (Or.inr rfl))
          · exact Or.inr rfl
          · exact Or.inl (Or.inr (carriedPairs_tgtS (by omega) x h'))
        refine blk_cons2 (blk_guard _ _ _ (Or.inr rfl) fun x hx => hLN0 x (by
          rw [hΛn1] at hx; exact hx)) ?_
        refine Blk.cons (blk_label n hLN0 fun x hx => by rw [hΛn]; exact hx) ?_
        -- the body
        refine Blk.append hBb' ?_
        -- the assignment at the back edge
        refine Blk.cons (blk_movI _ _ (by simp [opNames])) ?_
        refine Blk.append (blk_arrParMovesS _ _ _ _ (Or.inr rfl) fun a ha => ?_) ?_
        · obtain ⟨p, hp, hr, -, he⟩ := mem_arrPairsS ha
          obtain ⟨o, ho, he'⟩ := carriedPairs_srcS hp
          rw [he, he', ← sortName_of_arr hr]
          rcases hgoodB _ ho with h' | h'
          · exact Or.inl (Or.inl (Or.inr h'))
          · exact Or.inr h'
        refine Blk.append ((blk_parMoves _ _ _ (fun o ho => ?_) (fun o ho => ?_)
          (by simp)).mono (fun _ h => h) (fun x (hx : LN x) => ?_)) ?_
        · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ho
          rfl
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
          obtain ⟨p, hp, hr, rfl⟩ := mem_regPairsS hq
          obtain ⟨o, ho', he'⟩ := carriedPairs_srcS hp
          show _ ∨ E p.2.2
          rw [he']
          rcases hgoodB _ ho' with h' | h'
          · rw [sortName_of_reg hr] at h'
            exact Or.inl (Or.inl (Or.inl (Or.inr h')))
          · rw [sortName_of_reg hr] at h'
            exact Or.inr h'
        · exact Or.inl (Or.inl (Or.inl (Or.inl hx)))
        -- the advance, the back edge and the shift
        refine Blk.append (blk_advance _ _ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))) ?_
        refine blk_cons2 (blk_guard _ _ _ (Or.inr (Or.inr (Or.inl rfl))) fun x hx => by
          rw [hΛn] at hx; exact hx) ?_
        refine Blk.cons (blk_label (n + 1) (fun x hx => hx) fun x hx => by rw [hΛn1]; exact hx) ?_
        refine Blk.cons (blk_movI _ _ (by simp [opNames])) ?_
        refine (blk_typedMovesS (regName d) _ _ (Or.inr rfl) fun p hp => ?_).mono (fun _ h => h)
          fun x hx => ?_
        · rw [shiftPairs_eq, List.mem_reverse] at hp
          obtain ⟨o, ho, he⟩ := carriedPairs_srcS hp
          rw [he]
          exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (carS_of_zip ho)))))
        · rcases hx with h' | h'
          · exact Or.inl (Or.inl (Or.inl h'))
          · obtain ⟨p, hp, he⟩ := carriedPairs_tgtS (D := d) (cs := cs)
              (ops := (carriedRegs (d + 1) cs.length).map LOperand.reg)
              (by simp [carriedRegs]) x h'
            exact Or.inr ⟨p, by rw [shiftPairs_eq, List.mem_reverse]; exact hp, he⟩
      refine ⟨Λ, Blk.append hF (hKk'.mono (fun _ h => h) fun x hx => ?_)⟩
      rcases hx with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
  | @whileLoop Γ cs ts inits body k ihb ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      have hregT : ∀ t ∈ cs, isRegTy t = true := List.all_eq_true.mp hp.1.1
      intro d n r h hd E hE hS X hX
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      simp only [Exported.prepend, List.map_append] at hS ⊢
      have hSF := SymOK.append hS
      have hLb := exportR_labelsOK nArgs fn x86Data_guardsPlain body _ _ b hb
      have hLk := exportR_labelsOK nArgs fn x86Data_guardsPlain k _ _ rk hk
      have hlenB := exportR_res_length nArgs fn body _ _ b hb
      have hregB := exportR_res_isReg nArgs fn body _ _ b hb
      have hlenI := exprArgsHV_length d nArgs inits
      let car := carriedRegs d cs.length
      let LN : String → Prop := fun x => X x ∨ CarS d cs x
      have hLNin : ∀ x, InScopeS nArgs (cs ++ Γ) x → LN x := by
        intro x hx
        rcases inScopeS_append hx with h' | h'
        · exact Or.inl (hX _ h')
        · exact Or.inr (hd ▸ h')
      have hcar : ∀ x, CarS d cs x → x ∈ car := by
        rintro x ⟨j, t, hj, rfl⟩
        have hjl := (List.getElem?_eq_some_iff.mp hj).1
        rw [sortName_of_reg (hregT t (List.mem_of_getElem? hj))]
        exact mem_carriedRegs_of (by omega)
      have hSb : SymOK E (b.code.map (renArr tagA)) := fun i hi => hSF.1 i
        (mem_map_renArr_of_mem (fun j hj => by unfold whileFrame; simp [hj]) i hi)
      obtain ⟨Λb, hBb⟩ := ihb hp.1.2 hc.1 _ _ b hb (by simp [hd]; omega) E hE hSb LN hLNin
      obtain ⟨Λk, hKk⟩ := ihk hp.2 hc.2 _ _ rk hk (by simp [hd]; omega) E hE hSF.2 LN hLNin
      let Λ : LLabel → String → Prop := fun l =>
        if l = n then LN else if l < b.next then Λb l else Λk l
      have hΛn : ∀ x, Λ n x = LN x := fun x => by simp [Λ]
      have hBb' : Blk E Λ LN (b.code.map (renArr tagA))
          (fun x => LN x ∨ ResNS nArgs (HasBitType.bit (d := jasminDialect) :: cs) b.res x) :=
        blk_congr_labelsOK hBb hLb fun l h1 h2 => by
          simp only [Λ, ite_eq_right (show ¬(l = n) by omega), ite_eq_left h2]
      have hKk' : Blk E Λ LN (rk.code.map (renArr tagA))
          (fun x => LN x ∨ ResNS nArgs ts rk.res x) :=
        blk_congr_labelsOK hKk hLk fun l h1 h2 => by
          have := hLb.le
          simp only [Λ, ite_eq_right (show ¬(l = n) by omega), ite_eq_right (show ¬(l < b.next) by omega)]
      have hgoodB := goodRes (nArgs := nArgs) (ts := HasBitType.bit (d := jasminDialect) :: cs)
        (E := E) hE hregB
      obtain ⟨o, os, hro⟩ : ∃ o os, b.res = o :: os := by
        cases hr : b.res with
        | nil => rw [hr] at hlenB; simp at hlenB
        | cons o os => exact ⟨o, os, rfl⟩
      have hF : Blk E Λ X ((whileFrame d n cs.length
          (exprArgsHV d nArgs argName (fun _ => none) inits) b.code (b.res.headD (.imm 0))
          b.res.tail b.depth x86Data).map (renArr tagA)) LN := by
        unfold whileFrame
        dsimp only
        rw [x86_loopGuard (regName (b.depth + cs.length)) n]
        simp only [List.map_cons, List.map_nil, List.map_append, renArr_labelI,
          map_renArr_seedMoves, renArr_guardI_cmp, renArr_guardI_cond, map_renArr_parMoves,
          map_renArr_flagWord]
        unfold seedMoves
        refine Blk.append ((blk_movs (fun p : String × LOperand => p.1)
          (fun p : String × LOperand => p.2) _ fun p hp x hx => ?_).mono
          (fun _ h => h) (fun x (hx : LN x) => ?_)) ?_
        · have ho := (List.of_mem_zip hp).2
          obtain ⟨τ, hτ, y, hy, hok⟩ := exprArgsHV_memS hd inits p.2 ho
          rw [hy] at hx
          simp only [opNames, List.mem_singleton] at hx
          subst hx
          rw [sortName_of_reg (hregT τ hτ)] at hok
          rcases hok with h' | h'
          · exact Or.inr (hE _ ⟨_, h'.choose_spec.1, Or.inl h'.choose_spec.2⟩)
          · exact Or.inl (hX _ h')
        · rcases hx with h' | h'
          · exact Or.inl h'
          · have hm : (car.zip (exprArgsHV d nArgs argName (fun _ => none) inits)).map Prod.fst
                = car := List.map_fst_zip (by simp [car, carriedRegs_length]; omega)
            have h'' := hcar x h'
            rw [← hm] at h''
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h''
            exact Or.inr ⟨q, hq, rfl⟩
        refine Blk.cons (blk_label n (fun x hx => hx) fun x hx => by rw [hΛn]; exact hx) ?_
        refine Blk.append hBb' ?_
        refine Blk.append (blk_flagWord _ _ _ fun x hx => ?_) ?_
        · rw [hro] at hx
          simp only [List.headD_cons] at hx
          have ho := hregB o (by rw [hro]; exact List.mem_cons_self)
          rw [ho] at hx
          simp only [opNames, List.mem_singleton] at hx
          subst hx
          rcases hgoodB (HasBitType.bit (d := jasminDialect), o)
              (by rw [hro]; exact List.mem_cons_self) with h' | h'
          · rw [sortName_of_reg rfl] at h'
            exact Or.inl (Or.inr h')
          · rw [sortName_of_reg rfl] at h'
            exact Or.inr h'
        refine Blk.append ((blk_parMoves _ _ _ (fun o' ho' => hregB o' (List.mem_of_mem_tail ho'))
          (fun o' ho' => ?_) ?_).mono (fun _ h => h)
          (fun x (hx : LN x ∨ x = regName (b.depth + cs.length)) => ?_)) ?_
        · rw [hro, List.tail_cons] at ho'
          obtain ⟨τ, hτ⟩ := mem_zip_of_mem_right (l₁ := cs) ho' (by
            rw [hro] at hlenB; simp at hlenB; omega)
          have hτ' : (τ, o') ∈ (HasBitType.bit (d := jasminDialect) :: cs).zip b.res := by
            rw [hro, List.zip_cons_cons]
            exact List.mem_cons_of_mem _ hτ
          rcases hgoodB _ hτ' with h' | h'
          · rw [sortName_of_reg (hregT τ (List.of_mem_zip hτ).1)] at h'
            exact Or.inl (Or.inl (Or.inr h'))
          · rw [sortName_of_reg (hregT τ (List.of_mem_zip hτ).1)] at h'
            exact Or.inr h'
        · simp [carriedRegs_length, List.length_tail, hlenB]
        · rcases hx with h' | h'
          · exact Or.inl (Or.inl (Or.inl h'))
          · exact Or.inl (Or.inr h')
        exact (blk_guard _ _ _ (Or.inr rfl) fun x hx => Or.inl (by rw [hΛn] at hx; exact hx)).mono
          (fun _ h => h) fun x hx => Or.inl hx
      refine ⟨Λ, Blk.append hF (hKk'.mono (fun _ h => h) fun x hx => ?_)⟩
      rcases hx with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
  | @ifThenElse Γ rs ts cond thn els k iht ihe ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h hd E hE hS X hX
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      simp only [Exported.prepend, List.map_append] at hS ⊢
      have hSF := SymOK.append hS
      have hLt := exportR_labelsOK nArgs fn x86Data_guardsPlain thn _ _ t ht
      have hLe := exportR_labelsOK nArgs fn x86Data_guardsPlain els _ _ e he
      have hLk := exportR_labelsOK nArgs fn x86Data_guardsPlain k _ _ rk hk
      have hlenT := exportR_res_length nArgs fn thn _ _ t ht
      have hlenE := exportR_res_length nArgs fn els _ _ e he
      have hregT := exportR_res_isReg nArgs fn thn _ _ t ht
      have hregE := exportR_res_isReg nArgs fn els _ _ e he
      obtain ⟨cx, hcx, hcxok⟩ := resolveVar_okS (nArgs := nArgs) cond hd
      let JN : String → Prop := fun x => X x ∨ CarS d rs x
      have hJNin : ∀ x, InScopeS nArgs (rs ++ Γ) x → JN x := by
        intro x hx
        rcases inScopeS_append hx with h' | h'
        · exact Or.inl (hX _ h')
        · exact Or.inr (hd ▸ h')
      have hSt : SymOK E (t.code.map (renArr tagA)) := fun i hi => hSF.1 i
        (mem_map_renArr_of_mem (fun j hj => by unfold ifFrame; simp [hj]) i hi)
      have hSe : SymOK E (e.code.map (renArr tagA)) := fun i hi => hSF.1 i
        (mem_map_renArr_of_mem (fun j hj => by unfold ifFrame; simp [hj]) i hi)
      obtain ⟨Λt, hTt⟩ := iht hp.1.1 hc.1.1 _ _ t ht hd E hE hSt X hX
      obtain ⟨Λe, hEe⟩ := ihe hp.1.2 hc.1.2 _ _ e he hd E hE hSe X hX
      obtain ⟨Λk, hKk⟩ := ihk hp.2 hc.2 _ _ rk hk (by simp [hd]; omega) E hE hSF.2 JN hJNin
      have hle1 := hLt.le
      have hle2 := hLe.le
      let Λ : LLabel → String → Prop := fun l =>
        if l = n ∨ l = n + 1 then X else if l = n + 2 then JN
        else if l < t.next then Λt l else if l < e.next then Λe l else Λk l
      have hΛn : ∀ x, Λ n x = X x := fun x => by simp [Λ]
      have hΛn1 : ∀ x, Λ (n + 1) x = X x := fun x => by simp [Λ]
      have hΛn2 : ∀ x, Λ (n + 2) x = JN x := fun x => by simp [Λ]
      have hTt' : Blk E Λ X (t.code.map (renArr tagA)) (fun x => X x ∨ ResNS nArgs rs t.res x) :=
        blk_congr_labelsOK hTt hLt fun l h1 h2 => by
          simp only [Λ, ite_eq_right (show ¬(l = n ∨ l = n + 1) by omega),
            ite_eq_right (show ¬(l = n + 2) by omega), ite_eq_left h2]
      have hEe' : Blk E Λ X (e.code.map (renArr tagA)) (fun x => X x ∨ ResNS nArgs rs e.res x) :=
        blk_congr_labelsOK hEe hLe fun l h1 h2 => by
          simp only [Λ, ite_eq_right (show ¬(l = n ∨ l = n + 1) by omega),
            ite_eq_right (show ¬(l = n + 2) by omega), ite_eq_right (show ¬(l < t.next) by omega), ite_eq_left h2]
      have hKk' : Blk E Λ JN (rk.code.map (renArr tagA))
          (fun x => JN x ∨ ResNS nArgs ts rk.res x) :=
        blk_congr_labelsOK hKk hLk fun l h1 h2 => by
          simp only [Λ, ite_eq_right (show ¬(l = n ∨ l = n + 1) by omega),
            ite_eq_right (show ¬(l = n + 2) by omega), ite_eq_right (show ¬(l < t.next) by omega),
            ite_eq_right (show ¬(l < e.next) by omega)]
      have hgoodT := goodRes (nArgs := nArgs) (ts := rs) (E := E) hE hregT
      have hgoodE := goodRes (nArgs := nArgs) (ts := rs) (E := E) hE hregE
      have hF : Blk E Λ X ((ifFrame fn d n rs (resolveVar d nArgs argName (fun _ => none) cond)
          t.code t.res t.depth e.code e.res e.depth x86Data).map (renArr tagA)) JN := by
        unfold ifFrame
        rw [x86_zeroTrip (regName d) n (n + 1), x86_loopGuard (regName (d + rs.length)) (n + 2),
          hcx]
        simp only [List.map_cons, List.map_nil, List.map_append, renArr_movImmI, renArr_labelI,
          renArr_guardI_cmp, renArr_guardI_cond, map_renArr_flagWord, List.cons_append,
          List.nil_append]
        refine Blk.append (blk_flagWord _ _ _ fun x hx => ?_) ?_
        · simp only [opNames, List.mem_singleton] at hx
          subst hx
          rcases hcxok with h' | h'
          · exact Or.inr (hE _ ⟨_, h'.choose_spec.1, Or.inl h'.choose_spec.2⟩)
          · rw [sortName_of_reg rfl] at h'
            exact Or.inl (hX _ h')
        refine blk_cons2 (blk_guard _ _ _ (Or.inr rfl) fun x hx => Or.inl (by
          rw [hΛn1] at hx; exact hx)) ?_
        refine Blk.cons (blk_label n (fun x hx => Or.inl hx) fun x hx => by
          rw [hΛn]; exact hx) ?_
        refine Blk.append hTt' ?_
        refine Blk.append (blk_ifResMovesS _ _ _ _ (fun q hq => ?_) (by omega)) ?_
        · rcases hgoodT q hq with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr h'
        refine Blk.cons (blk_movI _ _ (by simp [opNames])) ?_
        refine blk_cons2 (blk_guard _ _ _ (Or.inr rfl) fun x hx => ?_) ?_
        · rw [hΛn2] at hx
          rcases hx with h' | h'
          · exact Or.inl (Or.inl (Or.inl h'))
          · exact Or.inl (Or.inr h')
        refine Blk.cons (blk_label (n + 1) (fun x hx => Or.inl (Or.inl (Or.inl hx)))
          fun x hx => by rw [hΛn1]; exact hx) ?_
        refine Blk.append hEe' ?_
        refine Blk.append (blk_ifResMovesS _ _ _ _ (fun q hq => ?_) (by omega)) ?_
        · rcases hgoodE q hq with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr h'
        refine blk_label (n + 2) (fun x hx => ?_) fun x hx => by rw [hΛn2]; exact hx
        rcases hx with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      refine ⟨Λ, Blk.append hF (hKk'.mono (fun _ h => h) fun x hx => ?_)⟩
      rcases hx with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'

/-! ## 11. The certificate of the tagged export -/

/-- **The certificate of the tagged export.** For the export `r` of a program over `Γ` whose
    bindings are in `opMemB` and which has no call, from the depth and the argument count
    `Γ.length` and the label `0` on x86, the tagged code `r.code.map (renArr tagA)` has a
    certificate of definite assignment at the argument names in both namespaces and its
    symbol operands (`ExportES`), which holds at the end the sorted name of every returned
    operand at its type, or that name is in `ExportES`. -/
theorem exportR_certS (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) :
    ∃ D, Cert (ExportES Γ.length (r.code.map (renArr tagA))) (r.code.map (renArr tagA)) D ∧
      ∀ q ∈ ts.zip r.res, D r.code.length (sortName q.1 (operandName q.2))
        ∨ ExportES Γ.length (r.code.map (renArr tagA)) (sortName q.1 (operandName q.2)) := by
  obtain ⟨Λ, hb⟩ := exportR_blkS Γ.length fn p hp hc _ 0 r h rfl
    (ExportES Γ.length (r.code.map (renArr tagA))) (fun x hx => Or.inl hx)
    (fun i hi x hx => Or.inr ⟨i, hi, hx⟩) (fun _ => False)
    (fun x ⟨s, t, h1, h2, _⟩ => by omega)
  obtain ⟨D, hC, hY⟩ := cert_of_blk hb
  refine ⟨D, hC, fun q hq => ?_⟩
  rcases goodRes (ts := ts) (E := ExportES Γ.length (r.code.map (renArr tagA)))
      (fun x hx => Or.inl hx) (exportR_res_isReg Γ.length fn p _ _ r h) q hq with h' | h'
  · left
    have := hY _ (Or.inr h')
    rwa [List.length_map] at this
  · exact Or.inr h'

/-- **The export mentions no tagged name** when its written names are untagged and it has no
    symbol-base load: the names it reads are argument names or written on every path to the
    reading position (`exportR_cert`). -/
theorem noTag_exportR (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r)
    (hsym : ∀ i ∈ r.code, symReads i = [])
    (hdef : ∀ i ∈ r.code, ∀ x ∈ defNames i.1, ¬ IsTag x) : NoTag r.code := by
  obtain ⟨D, hC, -⟩ := exportR_cert fn p h
  refine noTag_of_cert hC (exportR_noGoto _ _ p _ _ r h) ?_ hdef
    (RegionCoComplete.exportR_noShadow RegionCoComplete.x86Data_guardsNoShadow _ _ p hp hc _ _ r h)
  rintro x (⟨j, -, rfl⟩ | ⟨i, hi, hx⟩)
  · exact notTag_argName j
  · rw [hsym i hi] at hx
    cases hx

/-! ## 12. The tagged result copy -/

theorem isLopn_renArr (σ : String → String) {i : LinstrRM} (h : IsLopn i) :
    IsLopn (renArr σ i) := by
  rcases renArr_fst_cases σ i with h' | ⟨-, x, o, ss, h2⟩
  · obtain ⟨ds, o, ss, he⟩ := h
    exact ⟨ds, o, ss, by rw [h', he]⟩
  · exact ⟨_, _, _, h2⟩

theorem map_renArr_resCopyStep (src D : String) (m j : Nat) :
    (resCopyStep src D m j).map (renArr tagA) =
      [ movImmI copyIdx j
      , (.Lopn [.reg copyTmp] "LOADIDX" [.arrIdx (tagA src) copyIdx 8], .load 64 m)
      , (.Lopn [.reg (tagA (copyName D (j + 1)))] "STOREIDX"
          [.arrIdx (tagA (copyName D j)) copyIdx 8, .reg copyTmp], .store 64 m) ] := by
  simp only [resCopyStep, List.map_cons, List.map_nil, renArr_movImmI]
  simp [renArr, renLoad, renStore]

/-- The block of the first `k` words of the tagged result copy of `src` into `Dn`: from names
    `X` in which, with `E`, the tagged source and buffer are, to the names of `X` and the
    tagged version `copyName Dn k`. -/
theorem blk_resCopyS (src Dn : String) (M : Nat) {X : String → Prop}
    (hs : X (tagA src) ∨ E (tagA src)) (hD : X (tagA Dn) ∨ E (tagA Dn)) :
    ∀ k, Blk E Λ X (((List.range k).flatMap (resCopyStep src Dn M)).map (renArr tagA))
      (fun r => X r ∨ (0 < k ∧ r = tagA (copyName Dn k)))
  | 0 => blk_nil fun r hr => by simpa using hr
  | k + 1 => by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.map_append,
        map_renArr_resCopyStep]
      refine Blk.append (blk_resCopyS src Dn M hs hD k) ?_
      refine Blk.cons (blk_movI _ _ (by simp [opNames])) ?_
      refine Blk.cons (blk_opn _ _ _ _ fun x hx => ?_) ?_
      · simp only [List.flatMap_cons, List.flatMap_nil, opNames, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · rcases hs with h | h
          · exact Or.inl (Or.inl (Or.inl h))
          · exact Or.inr h
        · exact Or.inl (Or.inr rfl)
      refine (blk_opn _ _ _ _ fun x hx => ?_).mono (fun _ h => h) fun x hx => ?_
      · simp only [List.flatMap_cons, List.flatMap_nil, opNames, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hx
        rcases hx with rfl | rfl | rfl
        · cases k with
          | zero =>
              simp only [copyName, ↓reduceIte]
              rcases hD with h | h
              · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
              · exact Or.inr h
          | succ k => exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, rfl⟩)))
        · exact Or.inl (Or.inl (Or.inr rfl))
        · exact Or.inl (Or.inr (by simp [opNames]))
      · rcases hx with h | ⟨-, rfl⟩
        · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
        · exact Or.inr (by simp [opNames])

theorem isLopn_map_resCopyCode (src Dn : String) (M : Nat) :
    ∀ i ∈ (resCopyCode src Dn M).map (renArr tagA), IsLopn i := by
  intro i hi
  obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
  exact isLopn_renArr tagA (isLopn_resCopyCode src Dn M i' hi')

/-- **The certificate of the tagged code with the array result copy.** A certificate `D` of
    the tagged code `code.map (renArr tagA)` gives a certificate of the tagged code
    `code ++ regionLprogCopy a callee ts code res` that holds the names of `D` at the end of
    `code` at its end, when the tagged source and the tagged buffer of the copy decided by
    `resCopyOf` are in `D` at the end of `code` or in `E`. -/
theorem Cert.regionLprogCopyS {E : String → Prop} {code : List LinstrRM}
    {D : Nat → String → Prop} (hC : Cert E (code.map (renArr tagA)) D) (a : AbiNames)
    (callee : Option CalleeTab) (ts : List JasminTy) (res : List LOperand)
    (hcp : ∀ t src Dn m, callee = none → ts = [t] →
      resCopyOf a.outArg t code res = some (src, Dn, m) →
      (D code.length (tagA src) ∨ E (tagA src)) ∧ (D code.length (tagA Dn) ∨ E (tagA Dn))) :
    ∃ D', Cert E ((code ++ Haxc.regionLprogCopy a callee ts code res).map (renArr tagA)) D' ∧
      ∀ r, D code.length r →
        D' ((code ++ Haxc.regionLprogCopy a callee ts code res).map (renArr tagA)).length r := by
  have hnil : ∃ D', Cert E (code.map (renArr tagA) ++ []) D' ∧
      ∀ r, D code.length r → D' (code.map (renArr tagA) ++ []).length r :=
    ⟨D, by simpa using hC, fun r hr => by simpa using hr⟩
  rw [List.map_append]
  unfold Haxc.regionLprogCopy
  split
  · next t =>
      split
      · next src Dn m hcopy =>
          obtain ⟨hs, hD⟩ := hcp t src Dn m rfl rfl hcopy
          rw [← List.length_map (f := renArr tagA)] at hs hD
          obtain ⟨D', hC', hY⟩ := hC.append_blk (Λ := fun _ _ => False)
            (blk_resCopyS (E := E) src Dn m hs hD m) (isLopn_map_resCopyCode src Dn m)
          exact ⟨D', hC', fun r hr => hY r (Or.inl (by rwa [List.length_map]))⟩
      · simpa using hnil
  · simpa using hnil

/-! ## 13. The tagged code of the parts -/

theorem symReads_renArr {σ : String → String} {i : LinstrRM} (hn : NoShadow i) :
    symReads (renArr σ i) = symReads i := by
  obtain ⟨w, tag⟩ := i
  have hn' : shadowCall? w = none := hn
  cases tag <;> simp only [renArr, renCallW_of_none hn']
  · unfold renLoad; split
    · split_ifs with h
      · subst h; simp [symReads]
      · rfl
    · rfl
  · unfold renStore; split
    · split_ifs with h
      · subst h; simp [symReads]
      · rfl
    · rfl
  all_goals first
    | rfl
    | (unfold renZero; split
       · split_ifs with h
         · subst h; simp [symReads]
         · rfl
       · rfl)
    | (unfold renStoreImm; split
       · split_ifs with h
         · subst h; simp [symReads]
         · rfl
       · rfl)

/-- **Definite assignment of the tagged code of the parts at the argument names of the
    layout**: for the export `r` of a program over `Γ` whose bindings are in `opMemB`, which
    has no call and no symbol-base load, at a layout with at least `Γ.length` parameters and
    the result type `t` of the program, the tagged code of `regionCoCode` with its result
    copy has a certificate of definite assignment at the argument names of the layout in both
    namespaces. -/
theorem cert_regionCoCodeS (fn : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) (σ : AbiLayout)
    (nm : String → String) (hsym : ∀ i ∈ r.code, symReads i = [])
    (hlen : Γ.length ≤ σ.args.length) :
    ∃ D, Cert (ArgS σ.args.length)
      ((regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res)).map
        (renArr tagA)) D := by
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
    simp only [opNames, List.mem_singleton] at hx
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
  unfold regionCoCode
  split
  · exact ⟨D1, by rw [List.map_append, hmapM]; exact hC2⟩
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
    obtain ⟨D2, hC3, -⟩ := hC2.append_blk (Λ := fun _ _ => False)
      (blk_resCopyS src (argName j) m hs (Or.inr ⟨j, hjl, Or.inr rfl⟩) m)
      (isLopn_map_resCopyCode src (argName j) m)
    exact ⟨D2, by rw [List.map_append, List.map_append, hmapM]; exact hC3⟩

/-! ## 14. The input of the allocation -/

/-- **The input of the allocation keeps definite assignment and forward reachability.** For a
    code `C` of `NoTag` with nested jumps, no unconditional jump and register destinations,
    whose tagged code `C.map (renArr tagA)` has a certificate `D` of definite assignment at
    `E`, and a renaming `σ` of the array positions, the code
    `backEdgePins (pinSelfMoves (C.map (renArr σ)))` has a certificate of definite assignment
    at the names `untag σ '' E` that holds at its end the images under `untag σ` of the names
    of `D` at the end of `C` outside `untag σ '' E`; every one of its positions is forward
    reachable; and every one of its back edges targets a loop header. -/
theorem allocChain {E : String → Prop} {C : List LinstrRM} {D : Nat → String → Prop}
    (hC : Cert E (C.map (renArr tagA)) D) (hT : NoTag C) (hN : Nest C) (hG : NoGoto C)
    (hR : RegDsts C) (σ : String → String) :
    let C2 := Haxc.pinSelfMoves (C.map (renArr σ))
    let A := backEdgePins C2
    (∃ D', Cert (fun r => img (untag σ) E r ∨ ArrOnly C2 r) A D'
        ∧ ∀ r, img (untag σ) (D C.length) r → ¬ img (untag σ) E r → D' A.length r)
      ∧ (∀ k, k ≤ A.length → FwdPath A k) ∧ ∀ k q, BackEdge A k q → LoopHeader A q k := by
  intro C2 A
  have hC1 := Cert.renArrS hC hT σ
  obtain ⟨hN1, hG1, hR1⟩ := renArr_nest_noGoto_regDsts σ hN hG hR
  have hC2 := hC1.selfMovesPinned
  obtain ⟨hN2, hG2⟩ := pinSelfMoves_nest_noGoto hN1 hG1
  obtain ⟨D4, hC4, hend4⟩ := backEdgePins_cert hC2.defInit hG2 hN2 (regDsts_pinSelfMoves hR1)
  obtain ⟨hN4, hG4⟩ := backEdgePins_nest_noGoto hN2 hG2
  refine ⟨⟨D4, hC4, fun r hr hE => hend4 r fun ks hks => ?_⟩, fwdPath_of_noGoto hG4,
    fun _ _ hb => loopHeader_of_nest hN4 hb⟩
  have hr' : img (untag σ) (D (Haxc.pinSelfMoves (C.map (renArr σ))).length) r := by
    rw [length_pinSelfMoves, List.length_map]
    exact hr
  exact hC2.written hks r ⟨hr', hE⟩

/-- **The input of the allocation of a region** (`regionAllocCode`): the statement of
    `allocChain` at the coalescing renaming `canonMemrefName (Haxc.resAliasTab outs rr C)` of
    the out symbols `outs` and the result alias `rr`. -/
theorem regionAllocCode_chain {E : String → Prop} {C : List LinstrRM}
    {D : Nat → String → Prop} (hC : Cert E (C.map (renArr tagA)) D) (hT : NoTag C)
    (hN : Nest C) (hG : NoGoto C) (hR : RegDsts C) (outs : List (String × Nat))
    (rr : Option (String × String) := none) :
    (∃ D', Cert (fun r =>
          img (untag (canonMemrefName (Haxc.resAliasTab outs rr C))) E r
        ∨ ArrOnly (Haxc.pinSelfMoves (C.map (renArr
          (canonMemrefName (Haxc.resAliasTab outs rr C))))) r)
        (regionAllocCode C outs rr) D'
      ∧ ∀ r, img (untag (canonMemrefName (Haxc.resAliasTab outs rr C))) (D C.length) r →
        ¬ img (untag (canonMemrefName (Haxc.resAliasTab outs rr C))) E r →
          D' (regionAllocCode C outs rr).length r)
      ∧ (∀ k, k ≤ (regionAllocCode C outs rr).length → FwdPath (regionAllocCode C outs rr) k)
      ∧ ∀ k q, BackEdge (regionAllocCode C outs rr) k q →
          LoopHeader (regionAllocCode C outs rr) q k :=
  allocChain hC hT hN hG hR _

/-! ## 15. The tagged certificate of the webs -/

section WebsS

open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webRen webB webInstrB stepRen
  webB_instr webB_entry webB_exit webB_obs webB_live_pred)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (wrArr rdArr armOf
  ClassA coInstrB_iff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (arrReads arrWrite)

/-- A tagged name is the tag of a name. -/
theorem eq_tagA_of_isTag {y : String} (h : IsTag y) : ∃ z, y = tagA z := by
  unfold IsTag at h
  obtain ⟨rest, hr⟩ : ∃ rest, y.toList = '@' :: rest := by
    cases hl : y.toList with
    | nil => simp [hl] at h
    | cons c rest =>
        simp only [hl, List.head?_cons, Option.some.injEq] at h
        exact ⟨rest, by rw [h]⟩
  exact ⟨String.ofList rest, String.toList_inj.mp (by rw [toList_tagA, String.toList_ofList, hr])⟩

/-- The renaming of array positions keeps an instruction that is no shadow instruction of a
    call outside the shadow instructions. -/
theorem noShadow_renArr (σ : String → String) {i : LinstrRM} (h : NoShadow i) :
    NoShadow (renArr σ i) := by
  obtain ⟨w, tag⟩ := i
  have hn' : shadowCall? w = none := h
  show shadowCall? (renArr σ (w, tag)).1 = none
  cases tag <;> simp only [renArr, renCallW_of_none hn'] <;>
    (try simp only [renLoad, renStore, renZero, renStoreImm]) <;> (repeat' split) <;>
    simp_all [shadowCall?]

/-- The code renamed at its array positions has the paths of the code. -/
theorem path_map_renArr (σ : String → String) {C : List LinstrRM} {k : Nat} {ks : List Nat} :
    Path (C.map (renArr σ)) k ks ↔ Path C k ks := by
  have e : webRen (fun _ => σ) (fun _ => none) C = C.map (renArr σ) := by
    have hs : ∀ k i, stepRen (fun _ => σ) (fun _ => none) k i = σ := fun k i => by
      funext r
      simp [stepRen]
    apply List.ext_getElem (by simp [webRen])
    intro n h1 h2
    simp [webRen, hs]
  rw [← e]
  exact path_webRen _ _

/-- Outside a shadow instruction of a call, the shape conditions of the check do not depend on
    the renaming. -/
theorem classA_of_noShadow {σ ρ : String → String} {code : List LinstrRM}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {i : LinstrRM}
    (h : ClassA σ code aa ao i (armOf i)) (hn : NoShadow i) :
    ClassA ρ code aa ao i (armOf i) := by
  have hn' : shadowCall? i.1 = none := hn
  rcases ha : armOf i with ⟨dst, f, srcs⟩ | _ | _ | lbl | lbl | _ | _ <;> rw [ha] at h <;>
    simp only [ClassA] at h ⊢
  · rw [shadowCall_of_armOf ha] at hn'
    cases hn'
  · have hs : X86Backend.ImageCoalesceCfg.arrShapeB i = true := by
      by_contra hs
      revert ha
      unfold armOf
      rw [hn']
      simp only [hs, ↓reduceIte]
      repeat' split
      all_goals simp
    exact ⟨h.1, (RegionCoComplete.plainArrB_of_arrShapeB hs ρ).2, h.2.2⟩
  all_goals exact h

/-- Outside a shadow instruction of a call, the array names an instruction reads are the
    bases of its runtime-indexed loads and stores. -/
theorem mem_arrReads_of_rdArr {aa : String → Nat → Option Nat} {i : LinstrRM} {y : String}
    (hn : NoShadow i) (h : y ∈ rdArr aa i) : y ∈ arrReads i := by
  have hn' : shadowCall? i.1 = none := hn
  unfold rdArr at h
  rcases ha : armOf i with ⟨dst, f, srcs⟩ | _ | _ | lbl | lbl | _ | _ <;> rw [ha] at h <;>
    simp only [X86Backend.CoalesceComplete.rdArrA, List.not_mem_nil] at h
  · rw [shadowCall_of_armOf ha] at hn'
    cases hn'
  all_goals exact h

/-- The renamed instruction reads the image of an array base it reads. -/
theorem mem_useNames_renArr_arrReads (σ : String → String) {i : LinstrRM} {y : String}
    (h : y ∈ arrReads i) : σ y ∈ useNames (renArr σ i).1 := by
  obtain ⟨w, tag⟩ := i
  cases tag <;> simp only [arrReads] at h <;> simp only [renArr] <;>
    (try simp only [renLoad, renStore, renStoreImm]) <;> (repeat' split at h) <;>
    (repeat' split) <;>
    simp_all [loadStruct?, storeStruct?, storeImmStruct?, opNames]

/-- The symbol operands of an instruction are names it reads. -/
theorem symReads_sub_useNames {i : LinstrRM} {x : String} (h : x ∈ symReads i) :
    x ∈ useNames i.1 := by
  unfold symReads at h; split at h <;> (try split_ifs at h) <;> simp_all

/-- Outside a shadow instruction of a call, an array base an instruction reads is an array
    name it reads (`rdArr`). -/
theorem rdArr_of_arrReads {aa : String → Nat → Option Nat} {i : LinstrRM} {y : String}
    (hn : NoShadow i) (h : y ∈ arrReads i) : y ∈ rdArr aa i := by
  have hs : X86Backend.ImageCoalesceCfg.arrShapeB i = true := by
    obtain ⟨w, tag⟩ := i
    cases tag <;> simp only [arrReads] at h <;> (repeat' split at h) <;>
      simp_all [X86Backend.ImageCoalesceCfg.arrShapeB]
  unfold rdArr
  rw [armOf_of_arrShapeB hn hs]
  exact h

/-- **The reads of a renamed instruction.** Outside a shadow instruction of a call, on an
    instruction whose array zeroings read no name, a name read by `renArr σ i` is a name read
    by `i` and by every renaming `renArr ρ i`, or the image under `σ` of an array base that
    `i` reads. -/
theorem mem_useNames_renArr_cases (σ ρ : String → String) {i : LinstrRM} (hn : NoShadow i)
    (hz : ∀ a n, i.2 = .zero a n → useNames i.1 = []) {x : String}
    (hx : x ∈ useNames (renArr σ i).1) :
    (x ∈ useNames i.1 ∧ x ∈ useNames (renArr ρ i).1)
      ∨ ∃ y ∈ arrReads i, y ∈ useNames i.1 ∧ x = σ y := by
  obtain ⟨w, tag⟩ := i
  have hc : shadowCall? w = none := hn
  cases tag <;> simp only [renArr, renCallW_of_none hc, arrReads] at hx hz ⊢ <;>
    (try simp only [renLoad, renStore, renZero, renStoreImm] at hx ⊢) <;>
    (repeat' split at hx) <;> (repeat' split) <;>
    simp_all [loadStruct?, storeStruct?, storeImmStruct?, opNames] <;>
    first
    | (rcases hx with rfl | rfl | rfl <;> simp)
    | (obtain ⟨a, ha, hxa⟩ := hx
       have := hz a ha
       cases a <;> simp_all [renOpA])

/-- Outside a shadow instruction of a call, an untagged name the tagged instruction writes is
    written by the instruction other than as its array. -/
theorem defNames_renArr_tagA {i : LinstrRM} (hn : NoShadow i) {x : String} (hx : ¬ IsTag x)
    (h : x ∈ defNames (renArr tagA i).1) : x ∈ defNames i.1 ∧ arrWrite i ≠ some x := by
  obtain ⟨w, tag⟩ := i
  have hc : shadowCall? w = none := hn
  cases tag <;> simp only [renArr, renCallW_of_none hc] at h <;>
    (try simp only [renLoad, renStore, renZero, renStoreImm] at h) <;> (repeat' split at h) <;>
    simp_all [arrWrite, storeStruct?, zeroStruct?, storeImmStruct?, opNames, isTag_tagA]

/-- A tagged name written by the tagged instruction of `SortPlain` is the tag of the array of
    a store or an array zeroing. -/
theorem arrWrite_of_tagA_mem_defNames {i : LinstrRM} {y : String} (hn : SortPlain i)
    (h : tagA y ∈ defNames (renArr tagA i).1) : arrWrite i = some y := by
  obtain ⟨w, tag⟩ := i
  have hc : shadowCall? w = none := hn.noCall
  have hnm : ∀ x ∈ defNames w ++ useNames w, ¬ IsTag x := hn.names
  cases tag <;> simp only [renArr, renCallW_of_none hc] at h <;>
    (try simp only [renLoad, renStore, renZero, renStoreImm] at h) <;> (repeat' split at h) <;>
    first
    | exact absurd (isTag_tagA y) (hnm _ (List.mem_append_left _ h))
    | simp_all [arrWrite, storeStruct?, zeroStruct?, storeImmStruct?, opNames,
        tagA_injective.eq_iff]

/-- **The web of a live name along a path, at its array write.** For a map `w` accepted by
    `webB` and a path of the code to `k` along which the name `y` is live at `k`: either
    `w k y = y` and no instruction of the path writes `y` as an array, or an instruction of the
    path writes an array `d` whose step renaming is `w k y`. -/
theorem webB_path_wrArr {w : Nat → String → String} {code : List LinstrRM}
    {L : Nat → List String} {obs : List String} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hc : webB w code L obs aa ao = true) {k : Nat}
    {ks : List Nat} (hp : Path code k ks) {y : String} (hy : y ∈ L k) :
    (w k y = y ∧ ∀ j ∈ ks, ∀ i, code[j]? = some i → wrArr ao i ≠ some y)
      ∨ ∃ j ∈ ks, ∃ i d, code[j]? = some i ∧ wrArr ao i = some d ∧ stepRen w ao j i d = w k y := by
  induction hp with
  | nil => exact Or.inl ⟨webB_entry hc y hy, fun j hj => by simp at hj⟩
  | @cons k s ks i hp hi hs ih =>
      have hlp := webB_live_pred hc hi hs hy
      by_cases hw : wrArr ao i = some y
      · right
        refine ⟨k, List.mem_cons_self, i, y, hi, hw, ?_⟩
        rw [← hlp.2 hw]
        simp [stepRen, hw]
      · have hyk := mem_L_of_webSuccs hc hi hs hy hw
        rw [← hlp.1 hw]
        rcases ih hyk with ⟨h1, h2⟩ | ⟨j, hj, i', d, h1, h2, h3⟩
        · refine Or.inl ⟨h1, fun j hj i' hi' => ?_⟩
          rcases List.mem_cons.mp hj with rfl | hj
          · rw [hi] at hi'
            cases hi'
            exact hw
          · exact h2 j hj i' hi'
        · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, i', d, h1, h2, h3⟩

theorem getElem?_map_webRen (w : Nat → String → String) (ao : String → Option Nat)
    (code : List LinstrRM) (k : Nat) :
    ((webRen w ao code).map (renArr tagA))[k]? =
      code[k]?.map fun i => renArr (tagA ∘ stepRen w ao k i) i := by
  rw [List.getElem?_map, getElem?_webRen, Option.map_map]
  exact congrArg (Option.map · code[k]?) (funext fun i => renArr_renArr _ _ i)

/-- An untagged name written on a path of the tagged code is written on the path of the
    tagged webs. -/
theorem writtenOn_webRen_tagA_of_notTag {w : Nat → String → String} {ao : String → Option Nat}
    {code : List LinstrRM} (hN : NoTag code) {ks : List Nat} {x : String} (hx : ¬ IsTag x)
    (h : WrittenOn (code.map (renArr tagA)) ks x) :
    WrittenOn ((webRen w ao code).map (renArr tagA)) ks x := by
  obtain ⟨j, hj, i', hi', hx'⟩ := h
  rw [List.getElem?_map] at hi'
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hi'
  refine ⟨j, hj, renArr (tagA ∘ stepRen w ao j i) i, by rw [getElem?_map_webRen, hi]; rfl, ?_⟩
  rw [(names_renArr_factor _ (hN i (List.mem_of_getElem? hi))).2]
  exact List.mem_map.mpr ⟨x, hx', untag_of_not hx⟩

/-- The tagged webs write the tag of the step renaming of an array written on the path. -/
theorem writtenOn_webRen_tagA_of_wrArr {w : Nat → String → String} {ao : String → Option Nat}
    {code : List LinstrRM} {ks : List Nat} {j : Nat} (hj : j ∈ ks) {i : LinstrRM}
    (hi : code[j]? = some i) (hn : NoShadow i) {d : String} (hd : wrArr ao i = some d) :
    WrittenOn ((webRen w ao code).map (renArr tagA)) ks (tagA (stepRen w ao j i d)) := by
  refine ⟨j, hj, renArr (tagA ∘ stepRen w ao j i) i, by rw [getElem?_map_webRen, hi]; rfl, ?_⟩
  rw [wrArr_eq_arrWrite hn] at hd
  exact defNames_renArr_arrWrite (tagA ∘ stepRen w ao j i) hd

/-- **Definite assignment of the tagged webs.** A map `w` accepted by `webB` renames a code of
    `NoTag` whose register reads are written as registers on every path or in an untagged
    `E'` (`RegReads`), whose tagged code has definite assignment at `E₀`, into a code whose
    tagged code has definite assignment at every `E₁` containing `E₀`. -/
theorem defInit_webRen_tagA {E₀ E₁ : String → Prop} {w : Nat → String → String}
    {code : List LinstrRM} {L : Nat → List String} {obs : List String}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    {E' : String → Prop} (hc : webB w code L obs aa ao = true) (hR : RegReads E' aa ao code)
    (hEt : ∀ x, E' x → ¬ IsTag x) (hN : NoTag code)
    (h : DefInit E₀ (code.map (renArr tagA))) (hE : ∀ x, E₀ x → E₁ x) :
    DefInit E₁ ((webRen w ao code).map (renArr tagA)) := by
  intro k ks i' hp hi' x hx
  have hp0 : Path code k ks := (path_webRen w ao).mp ((path_map_renArr tagA).mp hp)
  rw [getElem?_map_webRen] at hi'
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hi'
  have hmem := List.mem_of_getElem? hi
  have hsp := hN i hmem
  have hpT : Path (code.map (renArr tagA)) k ks := (path_map_renArr tagA).mpr hp0
  have hiT : (code.map (renArr tagA))[k]? = some (renArr tagA i) := by
    rw [List.getElem?_map, hi]
    rfl
  have hwi := webB_instr hc hi
  unfold webInstrB at hwi
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hwi
  have hcls := (coInstrB_iff _ _ _ _ _ _ _).mp hwi.1.1
  rw [(names_renArr_factor _ hsp).1] at hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
  by_cases hzt : IsTag z
  · obtain ⟨y', rfl⟩ := eq_tagA_of_isTag hzt
    have hxu : (tagA ∘ stepRen w ao k i) y' ∈ useNames (renArr (tagA ∘ stepRen w ao k i) i).1 := by
      rw [(names_renArr_factor _ hsp).1]
      exact List.mem_map.mpr ⟨tagA y', hz, untag_tagA _ _⟩
    rw [untag_tagA]
    rcases hR k i hi _ (classA_of_noShadow hcls.1 hsp.noCall) _ hxu with hE' | hW | ⟨y, hy, -, hxy⟩
    · exact absurd (isTag_tagA _) (hEt _ hE')
    · obtain ⟨j, -, i2, h2, h3, -⟩ := hW ks hp0
      exact absurd (isTag_tagA _)
        ((hN i2 (List.mem_of_getElem? h2)).names _ (List.mem_append_left _ h3))
    have hyL : y ∈ L k := hcls.2.1.1 y hy
    have hσ : (tagA ∘ stepRen w ao k i) y = tagA (w k y) := by
      rw [Function.comp_apply, hwi.1.2 y hyL]
    rw [hxy, hσ]
    rcases webB_path_wrArr hc hp0 hyL with ⟨h1, h2⟩ | ⟨j, hj, i2, d, h1, h2, h3⟩
    · rw [h1]
      have hyT : tagA y ∈ useNames (renArr tagA i).1 :=
        mem_useNames_renArr_arrReads tagA (mem_arrReads_of_rdArr hsp.noCall hy)
      rcases h k ks _ hpT hiT _ hyT with h3 | ⟨j, hj, i2, h4, h5⟩
      · exact Or.inl (hE _ h3)
      · rw [List.getElem?_map] at h4
        obtain ⟨i3, hi3, rfl⟩ := Option.map_eq_some_iff.mp h4
        have hs3 := hN i3 (List.mem_of_getElem? hi3)
        have hw3 := arrWrite_of_tagA_mem_defNames hs3 h5
        rw [← wrArr_eq_arrWrite (ao := ao) hs3.noCall] at hw3
        exact absurd hw3 (h2 j hj i3 hi3)
    · right
      rw [← h3]
      exact writtenOn_webRen_tagA_of_wrArr hj h1 (hN i2 (List.mem_of_getElem? h1)).noCall h2
  · rw [untag_of_not hzt]
    rcases h k ks _ hpT hiT z hz with h3 | h3
    · exact Or.inl (hE _ h3)
    · exact Or.inr (writtenOn_webRen_tagA_of_notTag hN hzt h3)

/-- **The certificate of the tagged code of an exported code** (the statement of
    `exportR_certS` at every code of `RegionExp`), under `RegReads` and `NoTag` of the
    export. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.certS
    {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r) (hp : regionExportableB p = true) (hc : p.callFree = true)
    (hR : ∀ r0, exportR Γ.length fn p Γ.length 0 x86Data = some r0 →
      RegReads (ExportE Γ.length r0.code) (fun _ _ => none) (fun _ => none) r0.code)
    (hT : ∀ r0, exportR Γ.length fn p Γ.length 0 x86Data = some r0 → NoTag r0.code) :
    ∃ D, Cert (ExportES Γ.length (r.code.map (renArr tagA))) (r.code.map (renArr tagA)) D ∧
      ∀ q ∈ ts.zip r.res, D r.code.length (sortName q.1 (operandName q.2))
        ∨ ExportES Γ.length (r.code.map (renArr tagA)) (sortName q.1 (operandName q.2)) := by
  obtain ⟨r0, h0, hr | hr⟩ := h <;> subst r
  · exact exportR_certS fn p hp hc h0
  obtain ⟨D, hC, hres⟩ := exportR_certS fn p hp hc h0
  rcases regionWebs_webB ex r0 with he | ⟨w, hcw, he⟩
  · rw [he]
    exact ⟨D, hC, hres⟩
  rw [he]
  dsimp only
  have hN := hT r0 h0
  have hsymT : ∀ x, (∃ i ∈ r0.code, x ∈ symReads i) →
      ∃ i ∈ (webRen w (fun _ => none) r0.code).map (renArr tagA), x ∈ symReads i := by
    rintro x ⟨i, hi, hx⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
    refine ⟨_, List.mem_map_of_mem (by unfold webRen; exact List.mem_mapIdx.mpr ⟨k, hk, rfl⟩), ?_⟩
    rwa [symReads_renArr_eq, symReads_renArr_eq]
  have hE : ∀ x, ExportES Γ.length (r0.code.map (renArr tagA)) x →
      ExportES Γ.length ((webRen w (fun _ => none) r0.code).map (renArr tagA)) x := by
    rintro x (hx | ⟨i, hi, hx⟩)
    · exact Or.inl hx
    · obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
      rw [symReads_renArr_eq] at hx
      exact Or.inr (hsymT x ⟨i0, hi0, hx⟩)
  have hEt : ∀ x, ExportE Γ.length r0.code x → ¬ IsTag x := by
    rintro x (⟨j, -, rfl⟩ | ⟨i, hi, hx⟩)
    · exact notTag_argName j
    · exact (hN i hi).names x (List.mem_append_right _ (symReads_sub_useNames hx))
  have hD := defInit_webRen_tagA hcw (hR r0 h0) hEt hN hC.defInit hE
  refine ⟨_, hD.cert, fun q hq => ?_⟩
  by_cases hx' : ExportES Γ.length ((webRen w (fun _ => none) r0.code).map (renArr tagA))
      (sortName q.1 (operandName q.2))
  · exact Or.inr hx'
  left
  intro ks hp
  have hp0 : Path r0.code r0.code.length ks := by
    rw [length_webRen] at hp
    exact (path_webRen _ _).mp ((path_map_renArr tagA).mp hp)
  have hpT : Path (r0.code.map (renArr tagA)) (r0.code.map (renArr tagA)).length ks := by
    rw [List.length_map]
    exact (path_map_renArr tagA).mpr hp0
  have hq2 : q.2 ∈ r0.res := (List.of_mem_zip hq).2
  have hd : D (r0.code.map (renArr tagA)).length (sortName q.1 (operandName q.2)) := by
    rcases hres q hq with hd | hd
    · rwa [List.length_map]
    · exact absurd (hE _ hd) hx'
  have hwT := hC.written hpT _ hd
  cases ht : isRegTy q.1
  · rw [sortName_of_arr ht] at hwT ⊢
    have hobs : operandName q.2 ∈ regionWebsObs ex r0 :=
      List.mem_append_left _ (List.mem_map_of_mem hq2)
    rcases webB_path_wrArr hcw hp0 (webB_obs hcw _ hobs) with ⟨-, h2⟩ | ⟨j, hj, i2, d, h1, h2, h3⟩
    · obtain ⟨j, hj, i2, h4, h5⟩ := hwT
      rw [List.getElem?_map] at h4
      obtain ⟨i3, hi3, rfl⟩ := Option.map_eq_some_iff.mp h4
      have hs3 := hN i3 (List.mem_of_getElem? hi3)
      have hw3 := arrWrite_of_tagA_mem_defNames hs3 h5
      rw [← wrArr_eq_arrWrite (ao := fun _ => none) hs3.noCall] at hw3
      exact absurd hw3 (h2 j hj i3 hi3)
    · rw [webB_exit hcw _ hobs] at h3
      rw [← h3]
      exact writtenOn_webRen_tagA_of_wrArr hj h1 (hN i2 (List.mem_of_getElem? h1)).noCall h2
  · rw [sortName_of_reg ht] at hwT hx' ⊢
    obtain ⟨D0, hC0, hres0⟩ := exportR_cert fn p h0
    have hmem : operandName q.2 ∈ r0.res.flatMap opNames := by
      refine List.mem_flatMap.mpr ⟨q.2, hq2, ?_⟩
      rw [exportR_res_isReg _ _ p _ _ r0 h0 q.2 hq2]
      simp [opNames, operandName]
    rcases hres0 _ hmem with h3 | h3
    · obtain ⟨j, -, i2, h4, h5⟩ := hC0.written hp0 _ h3
      have hnt : ¬ IsTag (operandName q.2) :=
        (hN i2 (List.mem_of_getElem? h4)).names _ (List.mem_append_left _ h5)
      exact writtenOn_webRen_tagA_of_notTag hN hnt hwT
    · rcases h3 with ⟨j, hj, h4⟩ | h4
      · exact absurd (Or.inl ⟨j, hj, Or.inl h4⟩) hx'
      · exact absurd (Or.inr (hsymT _ h4)) hx'

/-- **An exported code mentions no tagged name** (the statement of `noTag_exportR` at every
    code of `RegionExp`), under `RegReads` of the export. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.noTag
    {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r) (hp : regionExportableB p = true) (hc : p.callFree = true)
    (hR : ∀ r0, exportR Γ.length fn p Γ.length 0 x86Data = some r0 →
      RegReads (ExportE Γ.length r0.code) (fun _ _ => none) (fun _ => none) r0.code)
    (hsym : ∀ i ∈ r.code, symReads i = [])
    (hdef : ∀ i ∈ r.code, ∀ x ∈ defNames i.1, ¬ IsTag x) : NoTag r.code := by
  obtain ⟨D, hC, -⟩ := h.cert hR
  refine noTag_of_cert hC h.noGoto ?_ hdef ?_
  · rintro x (⟨j, -, rfl⟩ | ⟨i, hi, hx⟩)
    · exact notTag_argName j
    · rw [hsym i hi] at hx
      cases hx
  · obtain ⟨r0, h0, hr | hr⟩ := h <;> subst r
    · exact RegionCoComplete.exportR_noShadow RegionCoComplete.x86Data_guardsNoShadow _ _ p hp
        hc _ _ r0 h0
    · exact forall_mem_regionWebs (P := NoShadow) (fun σ i hi => noShadow_renArr σ hi) ex r0 _ _
        (RegionCoComplete.exportR_noShadow RegionCoComplete.x86Data_guardsNoShadow _ _ p hp hc
          _ _ r0 h0)

/-- **The register reads of the export are written as registers on every path.** For the
    export `r` of a program without `call` that passes `regionExportableB`, on x86, whose
    written names are untagged and whose array zeroings read no name, a name read at the
    position `k` by a renaming of array positions of an instruction is an argument name or a
    symbol operand (`ExportE`), or is written other than as an array on every path to `k`, or
    is the image of an array base the instruction reads. The tagged certificate
    (`exportR_certS`) writes an untagged read name on every path at an untagged position,
    which is no array write. -/
theorem exportR_regReads (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r)
    (hdef : ∀ i ∈ r.code, ∀ x ∈ defNames i.1, ¬ IsTag x)
    (hz : ∀ i ∈ r.code, ∀ a n, i.2 = .zero a n → useNames i.1 = []) :
    RegReads (ExportE Γ.length r.code) (fun _ _ => none) (fun _ => none) r.code := by
  have hns := RegionCoComplete.exportR_noShadow RegionCoComplete.x86Data_guardsNoShadow _ _ p
    hp hc _ _ r h
  obtain ⟨D0, hC0, -⟩ := exportR_cert fn p h
  obtain ⟨D, hC, -⟩ := exportR_certS fn p hp hc h
  intro k i hi σ _ x hx
  have hmem := List.mem_of_getElem? hi
  rcases mem_useNames_renArr_cases σ tagA (hns i hmem) (hz i hmem) hx with
    ⟨hu, hut⟩ | ⟨y, hy, hyu, rfl⟩
  · by_cases hE : ExportE Γ.length r.code x
    · exact Or.inl hE
    refine Or.inr (Or.inl fun ks hpk => ?_)
    have hxt : ¬ IsTag x := by
      rcases hC0.use k i hi x hu with hd | hd
      · obtain ⟨j, -, i', hj, hx'⟩ := hC0.written hpk x hd
        exact hdef i' (List.mem_of_getElem? hj) x hx'
      · exact absurd hd hE
    have hpT : Path (r.code.map (renArr tagA)) k ks := (path_map_renArr tagA).mpr hpk
    have hiT : (r.code.map (renArr tagA))[k]? = some (renArr tagA i) := by
      rw [List.getElem?_map, hi]
      rfl
    rcases hC.defInit k ks _ hpT hiT x hut with hES | ⟨j, hj, i2, h4, h5⟩
    · exfalso
      rcases hES with ⟨j, hj, h1 | h1⟩ | ⟨i2, hi2, h2⟩
      · exact hE (Or.inl ⟨j, hj, h1⟩)
      · exact hxt (h1 ▸ isTag_tagA _)
      · obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi2
        rw [symReads_renArr_eq] at h2
        exact hE (Or.inr ⟨i0, hi0, h2⟩)
    · rw [List.getElem?_map] at h4
      obtain ⟨i3, hi3, rfl⟩ := Option.map_eq_some_iff.mp h4
      have hn3 := hns i3 (List.mem_of_getElem? hi3)
      obtain ⟨h6, h7⟩ := defNames_renArr_tagA hn3 hxt h5
      exact ⟨j, hj, i3, hi3, h6, by rw [wrArr_eq_arrWrite hn3]; exact h7⟩
  · exact Or.inr (Or.inr ⟨y, rdArr_of_arrReads (hns i hmem) hy, hyu, rfl⟩)

/-- **The certificate of definite assignment of an exported code** (`RegionExp.cert`) for a
    program without `call` that passes `regionExportableB`, whose export writes untagged
    names and has array zeroings that read no name. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.cert_of_exportR
    {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r) (hp : regionExportableB p = true) (hc : p.callFree = true)
    (hdef : ∀ r0, exportR Γ.length fn p Γ.length 0 x86Data = some r0 →
      ∀ i ∈ r0.code, ∀ x ∈ defNames i.1, ¬ IsTag x)
    (hz : ∀ r0, exportR Γ.length fn p Γ.length 0 x86Data = some r0 →
      ∀ i ∈ r0.code, ∀ a n, i.2 = .zero a n → useNames i.1 = []) :
    ∃ D, Cert (ExportE Γ.length r.code) r.code D ∧
      ∀ x ∈ r.res.flatMap opNames, D r.code.length x ∨ ExportE Γ.length r.code x :=
  h.cert fun r0 h0 => exportR_regReads fn p hp hc h0 (hdef r0 h0) (hz r0 h0)

/-- **Definite assignment of an exported code** (`RegionExp.defInit`) for a program without
    `call` that passes `regionExportableB`, whose export writes untagged names and has array
    zeroings that read no name. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.defInit_of_exportR
    {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r) (hp : regionExportableB p = true) (hc : p.callFree = true)
    (hdef : ∀ r0, exportR Γ.length fn p Γ.length 0 x86Data = some r0 →
      ∀ i ∈ r0.code, ∀ x ∈ defNames i.1, ¬ IsTag x)
    (hz : ∀ r0, exportR Γ.length fn p Γ.length 0 x86Data = some r0 →
      ∀ i ∈ r0.code, ∀ a n, i.2 = .zero a n → useNames i.1 = []) :
    DefInit (ExportE Γ.length r.code) r.code
      ∧ DefInitOut (ExportE Γ.length r.code) r.code (r.res.flatMap opNames)
      ∧ ∀ outs : List String,
          (∀ x ∈ outs, x ∈ r.res.flatMap opNames ∨ ExportE Γ.length r.code x) →
          ∀ x ∈ tabAt (liveRegTab r.code outs) 0,
            ExportE Γ.length r.code x ∨ ArrOnly r.code x :=
  h.defInit fun r0 h0 => exportR_regReads fn p hp hc h0 (hdef r0 h0) (hz r0 h0)

/-- **The certificate of the tagged code of an exported code** (`RegionExp.certS`) for a
    program without `call` that passes `regionExportableB`, whose export mentions no tagged
    name and has array zeroings that read no name. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.RegionExp.certS_of_exportR
    {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r) (hp : regionExportableB p = true) (hc : p.callFree = true)
    (hT : ∀ r0, exportR Γ.length fn p Γ.length 0 x86Data = some r0 → NoTag r0.code)
    (hz : ∀ r0, exportR Γ.length fn p Γ.length 0 x86Data = some r0 →
      ∀ i ∈ r0.code, ∀ a n, i.2 = .zero a n → useNames i.1 = []) :
    ∃ D, Cert (ExportES Γ.length (r.code.map (renArr tagA))) (r.code.map (renArr tagA)) D ∧
      ∀ q ∈ ts.zip r.res, D r.code.length (sortName q.1 (operandName q.2))
        ∨ ExportES Γ.length (r.code.map (renArr tagA)) (sortName q.1 (operandName q.2)) :=
  h.certS hp hc (fun r0 h0 => exportR_regReads fn p hp hc h0
    (fun i hi x hx => (hT r0 h0 i hi).names x (List.mem_append_left _ hx)) (hz r0 h0)) hT

end WebsS

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInitSort
