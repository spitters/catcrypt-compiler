/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomChainField
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapFinal
import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCertInj

/-!
# The renaming check on the field domain

The renaming check `renB` of the region gate reads the pairs `certArgs σ cert` of the
allocation certificate, the argument names with their locations, against the coalesced code.
It accepts when the targets of the pairs are distinct, are no sources, are no names of the
coalesced code and no argument names, when each source goes to its target, and when the code
is in the covered classes (`renB_intro`).

On a member of the field domain the certificate is `allocCertOf` of the allocation input. Its
targets are locations (`PhysName`): hardware registers, frame slots or vector registers, while
the names of the coalesced code are export register names and names beginning with `a`
(`CodeName`, from definite assignment and the coalescing renaming). Two argument names are read
by the liveness instruction at the entry of the allocation input, so the linear scan separates
them; without vector slots it does so at every number of live items
(`allocName_ne_of_liveAt_noVec`). The liveness instruction stays at the entry because the
store-thread canonicalization fixes the input: every store of the coalesced code writes its own
base, since the coalescing renaming sends the array a store writes and the array it reads to one
root (`AliasAgree`, from the store-chain shape of the export and of its webs).

## Main results

* `injHashB_of_injOn`: the converse of `injHashB_spec`.
* `renB_intro`: the renaming check from its conditions on the pairs.
* `allocName_ne_of_liveAt_noVec`: the allocation of a body without a call and without vector
  slots separates two names live at one trace position.
* `codeName_regionCoCode`: the names of the code with the result copies are names of the code.
* `storeOwnBase_of_class`, `aliasAgree_of_root`, `aliasAgree_append_copy`: the stores of the
  coalesced code write their own base.
* `codeFacts_export`, `codeFacts_webs`: these facts on the export of one chain of stores and on
  its webs.
* `regionAllocBody_pin`: the liveness instruction at the head of the allocation input.
* `fieldDom_renB`: the stage `G4` on the field domain.
* `fieldDom_coResultCopy`: the stage `G6` on the field domain.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (clsB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (mulxFree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (ReadAt WrAt ConsumedAt
  rdArr wrArr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf movesOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (renB injHashB injHashStep
  loopNames renOfH renMapOf renOfH_eq unren unren_of_not_target unren_target argBind noStoreB)

/-! ## 1. The injectivity fold -/

/-- The fold of `injHashStep` keeps a map whose entries are images of folded names. -/
theorem injHash_fold_isSome (f : String → String) : ∀ (Ns P : List String)
    (m : Std.HashMap String String),
    (∀ a ∈ P ++ Ns, ∀ b ∈ P ++ Ns, f a = f b → a = b) →
    (∀ k b, m[k]? = some b → b ∈ P ∧ f b = k) →
    (Ns.foldl (injHashStep f) (some m)).isSome = true
  | [], _, _, _, _ => rfl
  | x :: Ns, P, m, hinj, hm => by
      rw [List.foldl_cons]
      have hstep : ∃ m', injHashStep f (some m) x = some m'
          ∧ ∀ k b, m'[k]? = some b → b ∈ P ++ [x] ∧ f b = k := by
        simp only [injHashStep, Option.bind_some]
        cases hk : m[f x]? with
        | some b =>
          obtain ⟨hbP, hfb⟩ := hm _ _ hk
          have hbx : b = x := hinj b (List.mem_append_left _ hbP) x
            (List.mem_append_right _ List.mem_cons_self) hfb
          subst hbx
          refine ⟨m, by simp, fun k c hc => ?_⟩
          obtain ⟨h1, h2⟩ := hm k c hc
          exact ⟨List.mem_append_left _ h1, h2⟩
        | none =>
          refine ⟨m.insert (f x) x, rfl, fun k c hc => ?_⟩
          rw [Std.HashMap.getElem?_insert] at hc
          split at hc
          · rename_i he
            cases hc
            exact ⟨by simp, by simpa using he⟩
          · obtain ⟨h1, h2⟩ := hm k c hc
            exact ⟨List.mem_append_left _ h1, h2⟩
      obtain ⟨m', hm', hinv⟩ := hstep
      rw [hm']
      exact injHash_fold_isSome f Ns (P ++ [x]) m' (by simpa using hinj) hinv

/-- **The injectivity fold accepts every function injective on the folded names.** -/
theorem injHashB_of_injOn {f : String → String} {Ns : List String}
    (h : ∀ a ∈ Ns, ∀ b ∈ Ns, f a = f b → a = b) : injHashB f Ns = true := by
  unfold injHashB
  exact injHash_fold_isSome f Ns [] {} (by simpa using h) (fun k b hb => by simp at hb)

/-! ## 2. The renaming check from its conditions -/

/-- The renaming of a source of the pairs is the target of its first pair. -/
theorem renOf_exists (ps : List (String × String)) (n : String) :
    (∃ p ∈ ps, p.1 = n ∧ renOf ps n = p.2) ∨ ((∀ p ∈ ps, p.1 ≠ n) ∧ renOf ps n = n) := by
  unfold renOf
  cases hf : ps.find? (·.1 == n) with
  | none =>
    right
    refine ⟨fun p hp he => ?_, rfl⟩
    have := List.find?_eq_none.mp hf p hp
    simp [he] at this
  | some q =>
    left
    exact ⟨q, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, rfl⟩

/-- **The renaming check from its conditions on the pairs**: on code in the covered classes,
    pairs whose targets are distinct, no sources, no names of the code and no argument names,
    whose sources are not empty, each sent to its target by the renaming, at a layout whose
    copies of the parameter registers store no array, pass `renB` without seeds. -/
theorem renB_intro {σ : AbiLayout} {nm : String → String} {loop : List LinstrRM}
    {ps : List (String × String)}
    (hcls : ∀ i ∈ loop, (clsB i && mulxFree i) = true)
    (hnd : (ps.map Prod.snd).Nodup) (hsrc : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1)
    (hfst : ∀ p ∈ ps, renOf ps p.1 = p.2) (htgt : ∀ p ∈ ps, p.2 ∉ loopNames loop)
    (hemp : ∀ p ∈ ps, p.1 ≠ "")
    (hstore : (argBind σ nm).all noStoreB = true)
    (harg : ∀ j, j < σ.args.length → ∀ p ∈ ps, p.2 ≠ argName j) :
    renB σ nm [] loop ps = true := by
  have hr : renOfH (renMapOf ps) = renOf ps := funext (renOfH_eq ps)
  have hinj : ∀ a ∈ loopNames loop, ∀ b ∈ loopNames loop, renOf ps a = renOf ps b → a = b := by
    intro a ha b hb he
    rcases renOf_exists ps a with ⟨p, hp, rfl, hpa⟩ | ⟨-, hpa⟩ <;>
      rcases renOf_exists ps b with ⟨q, hq, rfl, hqb⟩ | ⟨-, hqb⟩
    · rw [hpa, hqb] at he
      have := List.inj_on_of_nodup_map hnd hp hq he
      rw [this]
    · rw [hpa, hqb] at he
      exact absurd (he ▸ hb) (htgt p hp)
    · rw [hpa, hqb] at he
      exact absurd (he.symm ▸ ha) (htgt q hq)
    · rwa [hpa, hqb] at he
  simp only [renB, hr, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq, Bool.not_eq_true', List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨(by simp), fun i hi => by simpa using hcls i hi⟩, injHashB_of_injOn hinj⟩, ?_⟩, hnd⟩,
    fun p hp q hq => hsrc p hp q hq⟩, hfst⟩, fun p hp => ?_⟩, (by simpa using hstore)⟩,
    fun j hj => ⟨?_, ?_⟩⟩
  · rcases renOf_exists ps "" with ⟨p, hp, he, -⟩ | ⟨-, h⟩
    · exact absurd he (hemp p hp)
    · exact h
  · simpa [Std.HashSet.contains_ofList] using htgt p hp
  · exact unren_of_not_target fun q hq => harg j hj q hq
  · rcases renOf_exists ps (argName j) with ⟨p, hp, he, hpa⟩ | ⟨-, hpa⟩
    · rw [hpa, unren_target hnd hp, he]
    · rw [hpa]
      exact unren_of_not_target fun q hq => harg j hj q hq

/-! ## 3. Injectivity of the allocation without vector slots -/

section NoVec

open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRA
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCertInj

/-- Without vector slots the vector half of the class-aware assignment is empty. -/
theorem vecHalf_noVec {tr : List PhysEvent} {vecArr : Array Bool} (reservedVec : List Nat)
    (hv : ∀ s, slotIsVec vecArr s = false) : vecHalf tr vecArr reservedVec = [] := by
  unfold vecHalf
  rw [List.filter_eq_nil_iff.mpr fun it _ => by simp [hv]]
  rfl

/-- **The class-aware assignment without vector slots is collision-free**, at every number of
    live items. -/
theorem physAssignClassed_no_collision_noVec (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved reservedVec : List Nat) (hv : ∀ s, slotIsVec vecArr s = false)
    {t₁ t₂ p : Nat} (hne : t₁ ≠ t₂) {split : Option SplitCfg}
    (hu1 : t₁ < physUniverse tr) (hu2 : t₂ < physUniverse tr)
    (h1 : physLoc (physAssignClassed tr vecArr reserved reservedVec x86Abi split) t₁ = some p)
    (h2 : physLoc (physAssignClassed tr vecArr reserved reservedVec x86Abi split) t₂ = some p) :
    ¬ physRangesOverlap (physLiveRange tr t₁) (physLiveRange tr t₂) := by
  rw [physAssignClassed_eq, vecHalf_noVec reservedVec hv, List.map_nil, List.append_nil] at h1 h2
  exact gpHalf_no_collision tr vecArr reserved split hne hu1 hu2 h1 h2

/-- The table of the class-aware assignment without vector slots is collision-free. -/
theorem physTableClassed_no_collision_noVec (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved reservedVec : List Nat) (hv : ∀ s, slotIsVec vecArr s = false)
    {t₁ t₂ : Nat} (hne : t₁ ≠ t₂)
    (hu1 : t₁ < physUniverse tr) (hu2 : t₂ < physUniverse tr)
    (hl1 : ∃ it ∈ physLiveItems tr, it.1 = t₁)
    (hl2 : ∃ it ∈ physLiveItems tr, it.1 = t₂)
    (hov : physRangesOverlap (physLiveRange tr t₁) (physLiveRange tr t₂))
    {split : Option SplitCfg} :
    physMapTabled (physTableClassed tr vecArr reserved reservedVec x86Abi split) t₁
      ≠ physMapTabled (physTableClassed tr vecArr reserved reservedVec x86Abi split) t₂ := by
  intro heq
  cases h1 : physLoc (physAssignClassed tr vecArr reserved reservedVec x86Abi split) t₁ with
  | none => exact physAssignClassed_physLoc_live tr vecArr reserved reservedVec hl1 h1
  | some p₁ =>
    cases h2 : physLoc (physAssignClassed tr vecArr reserved reservedVec x86Abi split) t₂ with
    | none => exact physAssignClassed_physLoc_live tr vecArr reserved reservedVec hl2 h2
    | some p₂ =>
      have e1 := physMapTabled_physTableClassed_of_physLoc (vecArr := vecArr) hu1 h1
      have e2 := physMapTabled_physTableClassed_of_physLoc (vecArr := vecArr) hu2 h2
      have hpp : p₁ = p₂ := by rw [← e1, ← e2]; exact heq
      subst hpp
      exact physAssignClassed_no_collision_noVec tr vecArr reserved reservedVec hv hne hu1 hu2
        h1 h2 hov

/-- **The allocation of a body without a call and without vector slots separates two names
    live at one trace position**, at every number of live items. -/
theorem allocName_ne_of_liveAt_noVec {body : Lcmd} {outStoreMap : OutStoreMap}
    {reservedVec : List Nat} {split : Option SplitCfg} {a b : String} {pos : Nat}
    (hc : bodyHasCall body = false) (hv : ∀ s, slotIsVec (bodyVecSlots body) s = false)
    (ha : a ∈ bodyNames body) (hb : b ∈ bodyNames body) (hne : a ≠ b)
    (hla : LiveAt (bodyTraceOut body outStoreMap) pos (nameSlot body a))
    (hlb : LiveAt (bodyTraceOut body outStoreMap) pos (nameSlot body b)) :
    allocName body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec x86Abi split)) a
      ≠ allocName body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec x86Abi split)) b := by
  obtain ⟨hu1, hl1⟩ := live_out_of_mem_bodyNames (outStoreMap := outStoreMap) ha
  obtain ⟨hu2, hl2⟩ := live_out_of_mem_bodyNames (outStoreMap := outStoreMap) hb
  have hsl : nameSlot body a ≠ nameSlot body b := fun h => hne (nameSlot_injOn ha hb h)
  have hT := physTableClassed_no_collision_noVec _ _ (bodyReservedGP body) reservedVec hv hsl hu1 hu2 hl1 hl2
    (overlap_of_liveAt hla hlb) (split := split)
  have hs : bodyStraightCall body = false := by
    unfold bodyStraightCall; simp [hc]
  have hid : straightCallComposeTable body (physTableOut body outStoreMap reservedVec x86Abi split)
      = physTableOut body outStoreMap reservedVec x86Abi split := by
    unfold straightCallComposeTable; rw [hs]; rfl
  unfold allocName
  rw [hc, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, hid]
  intro h
  exact hT (physRegName_inj h)

end NoVec

/-! ## 4. Physical names and the names of the code -/

section Names

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames defNames)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapLive (ExportRegName)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInit (Cert NoGoto fwdPath_of_noGoto)

/-- A name of a location of the allocation: a hardware register name, a frame-slot name or a
    vector register name. -/
def PhysName (y : String) : Prop :=
  isHwRegName y = true ∨ isFrameSlotName y = true ∨ y ∈ vectorRegNames

/-- A name of the exported code: an export register name or a name whose first character is
    `a`, as the argument names and their copy versions. -/
def CodeName (x : String) : Prop := ExportRegName x ∨ x.toList.head? = some 'a'

theorem codeName_argName (j : Nat) : CodeName (argName j) :=
  Or.inr (by simp [argName, String.toList_append])

theorem codeName_copyName {D : String} (hD : D.toList.head? = some 'a') (j : Nat) :
    CodeName (copyName D j) := by
  refine Or.inr ?_
  unfold copyName
  split
  · exact hD
  · obtain ⟨c, l, hl⟩ : ∃ c l, D.toList = c :: l := by
      cases h : D.toList with
      | nil => rw [h] at hD; cases hD
      | cons c l => exact ⟨c, l, rfl⟩
    rw [hl] at hD
    simp only [List.head?_cons, Option.some.injEq] at hD
    simp [String.toList_append, hl, hD]

theorem head_of_hasPrefix {n p : String} (h : hasPrefix n p = true) {c : Char}
    (hp : p.toList.head? = some c) : n.toList.head? = some c := by
  unfold hasPrefix at h
  cases hq : p.toList with
  | nil => rw [hq] at hp; cases hp
  | cons c' l =>
    rw [hq] at hp h
    cases hn : n.toList with
    | nil => rw [hn] at h; simp [List.isPrefixOf] at h
    | cons d l' =>
      rw [hn] at h
      simp only [List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at h
      simp only [List.head?_cons, Option.some.injEq] at hp ⊢
      rw [← hp, h.1]

theorem codeName_iff (x : String) : CodeName x ↔
    (x.toList.head? = some 'r' ∨ x.toList.head? = some 'L' ∨ x.toList.head? = some 'a') := by
  unfold CodeName ExportRegName
  tauto

/-- **A physical name is no name of the code.** -/
theorem PhysName.not_codeName {y : String} (h : PhysName y) : ¬ CodeName y := by
  rw [codeName_iff]
  rcases h with h | h | h
  · have key : ∀ z ∈ hwRegNames, ¬ (z.toList.head? = some 'r' ∨ z.toList.head? = some 'L'
        ∨ z.toList.head? = some 'a') := by decide
    exact key y (by simpa [isHwRegName] using h)
  · unfold isFrameSlotName at h
    simp only [Bool.or_eq_true] at h
    have hk : ∀ c, y.toList.head? = some c → c ≠ 'r' ∧ c ≠ 'L' ∧ c ≠ 'a' → ¬ (y.toList.head?
        = some 'r' ∨ y.toList.head? = some 'L' ∨ y.toList.head? = some 'a') := by
      intro c hc hne hor
      rw [hc] at hor
      simp only [Option.some.injEq] at hor
      rcases hor with rfl | rfl | rfl <;> simp at hne
    rcases h with ((h | h) | h) | h
    · exact hk 'k' (head_of_hasPrefix h (by decide)) (by decide)
    · exact hk 'k' (head_of_hasPrefix h (by decide)) (by decide)
    · exact hk 'q' (head_of_hasPrefix h (by decide)) (by decide)
    · exact hk 'm' (head_of_hasPrefix h (by decide)) (by decide)
  · have key : ∀ z ∈ vectorRegNames, ¬ (z.toList.head? = some 'r' ∨ z.toList.head? = some 'L'
        ∨ z.toList.head? = some 'a') := by decide
    exact key y h

theorem PhysName.ne_empty {y : String} (h : PhysName y) : y ≠ "" := by
  rintro rfl
  rcases h with h | h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- The names of an instruction are its written and its read names. -/
theorem mem_instrNames {w : LinstrR} {x : String} (h : x ∈ instrNames w) :
    x ∈ defNames w ∨ x ∈ useNames w := by
  cases w <;> simp_all [instrNames, defNames, useNames, List.flatMap_append]

/-- **The names of code with a certificate of definite assignment** satisfy every predicate
    that holds of the names read before a write and of the written names. -/
theorem names_of_cert {P : String → Prop} {E : String → Prop} {C : List LinstrRM}
    {D : Nat → String → Prop} (hC : Cert E C D) (hG : NoGoto C) (hE : ∀ x, E x → P x)
    (hdef : ∀ i ∈ C, ∀ x ∈ defNames i.1, P x) : ∀ i ∈ C, ∀ x ∈ instrNames i.1, P x := by
  intro i hi x hx
  rcases mem_instrNames hx with hx | hx
  · exact hdef i hi x hx
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    have hlt := (List.getElem?_eq_some_iff.mp hk).1
    rcases hC.use k i hk x hx with h | h
    · obtain ⟨ks, hp⟩ := (fwdPath_of_noGoto hG k hlt.le).path
      obtain ⟨j, -, i', hj, hx'⟩ := hC.written hp x h
      exact hdef i' (List.mem_of_getElem? hj) x hx'
    · exact hE x h

end Names

/-! ## 5. The names of the coalesced code -/

section CoNames

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames defNames)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapLive (ExportRegName
  exportRegName_copyIdx exportRegName_copyTmp cert_regionCoCode)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInit (NoGoto isGoto_of_isLopn
  isLopn_resCopyCode)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO aliasTab
  aliasTabRes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr renCallW_of_none)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom (Under under_renLoad
  under_renStore under_renStoreImm under_renZero base_mem_instrNames)

/-- **The coalescing renaming keeps a predicate of the names of the code**: the fold of the
    alias steps from a table whose images satisfy `P` sends a name satisfying `P` to a name
    satisfying `P`, when every name of the code satisfies `P` and no instruction is the shadow
    of a call. -/
theorem alias_foldl_pred {P : String → Prop} (outs : List (String × Nat)) :
    ∀ (L : List LinstrRM) (M : Std.HashMap String String),
      (∀ i ∈ L, ∀ x ∈ instrNames i.1, P x) → (∀ i ∈ L, LprogIsa.shadowCall? i.1 = none) →
      (∀ x, P x → P (canonMemrefName M x)) →
      ∀ x, P x → P (canonMemrefName (L.foldl (aliasStepO outs) M) x)
  | [], _, _, _, hM => hM
  | i :: L, M, hL, hs, hM => by
    rw [List.foldl_cons]
    refine alias_foldl_pred outs L _ (fun j hj => hL j (List.mem_cons_of_mem _ hj))
      (fun j hj => hs j (List.mem_cons_of_mem _ hj)) ?_
    have hn := hL i List.mem_cons_self
    unfold aliasStepO
    rw [hs i List.mem_cons_self]
    dsimp only
    split
    · next dst opn base _ _ rest heq =>
      have hb : P base := hn base (by rw [heq]; exact base_mem_instrNames)
      split_ifs
      · intro x hx
        unfold canonMemrefName
        rw [Std.HashMap.getD_insert]
        split
        · exact hM base hb
        · exact hM x hx
      · exact hM
    · next dst opn base rest heq =>
      have hb : P base := hn base (by rw [heq]; simp [instrNames,
        JasminLsemExportRewrites.opNames])
      split_ifs
      · intro x hx
        unfold canonMemrefName
        rw [Std.HashMap.getD_insert]
        split
        · exact hM base hb
        · exact hM x hx
      · exact hM
    · exact hM

/-- The renaming of the array positions of an instruction that is no shadow of a call
    mentions the names of the instruction and their images. -/
theorem under_renArr (ρ : String → String) {i : LinstrRM}
    (hs : LprogIsa.shadowCall? i.1 = none) : Under ρ i.1 (renArr ρ i).1 := by
  obtain ⟨w, t⟩ := i
  unfold renArr
  split
  · exact under_renLoad ρ w
  · exact under_renStore ρ w
  · exact under_renZero ρ w
  · exact under_renStoreImm ρ w
  · rw [renCallW_of_none hs]
    exact fun x hx => Or.inl hx

/-- **The names of the code with the result copies are names of the code**, for an exported
    code of a program without `call` that passes `regionExportableB`, at a layout without a
    register result. -/
theorem codeName_regionCoCode (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {ex : List String} {r : Exported}
    (h : RegionExp fn p ex r) (σ : AbiLayout) (nm : String → String) (t : JasminTy)
    (hsym : ∀ i ∈ r.code, RegionExportDefInit.symReads i = [])
    (hlen : Γ.length ≤ σ.args.length) (hret : regionRet σ nm t r.res = none) :
    ∀ i ∈ regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res),
      ∀ x ∈ instrNames i.1, CodeName x := by
  obtain ⟨D, hC⟩ := cert_regionCoCode fn p hp hc h σ nm t hsym hlen
  have hdef := h.defsR hp hc
  have hGr := h.noGoto
  have hcopy : ∀ src D m, regionCopy σ nm t none r.code r.res = some (src, D, m) →
      ∀ i ∈ resCopyCode src D m, JasminLsemMemLoop.IsLopn i ∧ ∀ x ∈ defNames i.1, CodeName x := by
    intro src D m hcp i hi
    obtain ⟨-, -, -, ⟨j, -, -, -, rfl⟩, -, -⟩ := regionCopy_some hcp
    refine ⟨isLopn_resCopyCode src _ m i hi, fun x hx => ?_⟩
    obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hi
    simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · simp [ExportRegions.movImmI, ExportRegions.movI, defNames,
        JasminLsemExportRewrites.opNames] at hx
      subst hx
      exact Or.inl exportRegName_copyIdx
    · simp [defNames, JasminLsemExportRewrites.opNames] at hx
      subst hx
      exact Or.inl exportRegName_copyTmp
    · simp [defNames, JasminLsemExportRewrites.opNames] at hx
      subst hx
      exact codeName_copyName (by simp [argName, String.toList_append]) _
  have hparts : ∀ i ∈ regionCoCode σ nm t r.code r.res (regionCopy σ nm t none r.code r.res),
      i ∈ r.code ∨ (JasminLsemMemLoop.IsLopn i ∧ ∀ x ∈ defNames i.1, CodeName x) := by
    intro i hi
    unfold regionCoCode at hi
    rw [hret] at hi
    split at hi
    · simp only [Option.toList_none, JasminLsemRenameLoop.movesOf, List.map_nil,
        List.append_nil] at hi
      exact Or.inl hi
    · rename_i src D m hcp
      simp only [Option.toList_none, JasminLsemRenameLoop.movesOf, List.map_nil,
        List.append_nil] at hi
      rcases List.mem_append.mp hi with h' | h'
      · exact Or.inl h'
      · exact Or.inr (hcopy src D m hcp i h')
  refine names_of_cert hC (fun i hi => ?_) (fun x hx => ?_) (fun i hi => ?_)
  · rcases hparts i hi with h' | h'
    · exact hGr i h'
    · exact isGoto_of_isLopn h'.1
  · obtain ⟨j, -, rfl⟩ := RegionAllocMapLive.exists_of_isArgNameB hx
    exact codeName_argName j
  · rcases hparts i hi with h' | h'
    · exact fun x hx => Or.inl (hdef i h' x hx)
    · exact h'.2

end CoNames

/-! ## 6. Stores that write their own base after the coalescing -/

section OwnBase

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO aliasTab)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (rdArr wrArr)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapFinal (StoreOwnBase)

/-- **The alias step of an instruction by its array write**: an instruction that writes no
    array keeps every table under every renaming of its array positions, and one that writes
    `d` reads one array `b` and sends the renamed `d` to the root of the renamed `b`. -/
def StoreClass (i : LinstrRM) : Prop :=
  LprogIsa.shadowCall? i.1 = none
    ∧ (wrArr (fun _ => none) i = none → ∀ M ρ, aliasStepO [] M (renArr ρ i) = M)
    ∧ ∀ d, wrArr (fun _ => none) i = some d → ∃ b, rdArr (fun _ _ => none) i = [b]
      ∧ ∀ M ρ, aliasStepO [] M (renArr ρ i) = M.insert (ρ d) (M.getD (ρ b) (ρ b))

/-- **A store of the renamed code writes its own base** when the renaming sends the array an
    instruction of the class `StoreClass` writes and the array it reads to one name. -/
theorem storeOwnBase_of_class {i : LinstrRM} (hc : StoreClass i) {ρ : String → String}
    (hag : ∀ d b, wrArr (fun _ => none) i = some d → rdArr (fun _ _ => none) i = [b] →
      ρ d = ρ b) :
    StoreOwnBase (renArr ρ i).1 := by
  intro dst opn base x s rest he hs
  have hsh : LprogIsa.shadowCall? (renArr ρ i).1 = none :=
    RegionCoComplete.noShadow_renArr ρ hc.1
  have hstep : ∀ M, aliasStepO [] M (renArr ρ i) = M.insert dst (M.getD base base) := by
    intro M
    unfold aliasStepO
    rw [hsh]
    dsimp only
    rw [he]
    simp [hs]
  cases hw : wrArr (fun _ => none) i with
  | none =>
    have h1 := hc.2.1 hw {} ρ
    rw [hstep] at h1
    have := congrArg (fun M : Std.HashMap String String => M.contains dst) h1
    simp at this
  | some d =>
    obtain ⟨b, hb, hM⟩ := hc.2.2 d hw
    have h1 := hM {} ρ
    rw [hstep] at h1
    have hc1 := congrArg (fun M : Std.HashMap String String => M.contains dst) h1
    have hg1 := congrArg (fun M : Std.HashMap String String => M.getD dst dst) h1
    simp only [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
      beq_self_eq_true, Bool.true_eq, beq_iff_eq] at hc1
    simp only [Std.HashMap.getD_insert, Std.HashMap.getD_empty, beq_self_eq_true, ite_true,
      hc1] at hg1
    rw [← hc1, hag d b hw hb, ← hg1]

/-- **The coalescing renaming of the code sends the array a store writes and the array it reads
    to one root.** -/
def AliasAgree (C : List LinstrRM) : Prop :=
  ∀ i ∈ C, ∀ d b, wrArr (fun _ => none) i = some d → rdArr (fun _ _ => none) i = [b] →
    canonMemrefName (aliasTab [] C) d = canonMemrefName (aliasTab [] C) b

/-- **Agreement from one root**: when every written array goes to the root `z`, every other
    name is fixed, and the array each store reads is written somewhere or is `z`. -/
theorem aliasAgree_of_root {C : List LinstrRM} {z : String}
    (hW1 : ∀ w d, WrAt C (fun _ => none) w d → canonMemrefName (aliasTab [] C) d = z)
    (hW2 : ∀ n, (∀ w, ¬ WrAt C (fun _ => none) w n) → canonMemrefName (aliasTab [] C) n = n)
    (hb : ∀ (k : Nat) i d b, C[k]? = some i → wrArr (fun _ => none) i = some d →
      rdArr (fun _ _ => none) i = [b] → (∃ k', WrAt C (fun _ => none) k' b) ∨ b = z) :
    AliasAgree C := by
  intro i hi d b hd hb'
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
  rw [hW1 k d ⟨i, hk, hd⟩]
  rcases hb k i d b hk hd hb' with ⟨k', hk'⟩ | rfl
  · rw [hW1 k' b hk']
  · by_cases hw : ∃ k', WrAt C (fun _ => none) k' b
    · obtain ⟨k', hk'⟩ := hw
      rw [hW1 k' b hk']
    · rw [hW2 b fun w h => hw ⟨w, h⟩]

/-- **Agreement after the result copy**: the copy sends its versions to the root of the result
    buffer, and keeps the roots of the arrays of the code, which are no versions. -/
theorem aliasAgree_append_copy {C : List LinstrRM} {src D : String} {m : Nat}
    (h : AliasAgree C)
    (hn : ∀ i ∈ C, ∀ d b, wrArr (fun _ => none) i = some d → rdArr (fun _ _ => none) i = [b] →
      ∀ k, k < m → d ≠ copyName D (k + 1) ∧ b ≠ copyName D (k + 1)) :
    AliasAgree (C ++ resCopyCode src D m) := by
  have hT : aliasTab [] (C ++ resCopyCode src D m)
      = (resCopyCode src D m).foldl (aliasStepO []) (aliasTab [] C) := by
    simp [aliasTab, List.foldl_append]
  intro i hi d b hd hb
  unfold canonMemrefName
  rw [hT, getD_foldl_resCopyCode, getD_foldl_resCopyCode]
  rcases List.mem_append.mp hi with hi | hi
  · have e1 : ¬ ∃ j, j < m ∧ d = copyName D (j + 1) := fun ⟨j, hj, he⟩ => (hn i hi d b hd hb j hj).1 he
    have e2 : ¬ ∃ j, j < m ∧ b = copyName D (j + 1) := fun ⟨j, hj, he⟩ => (hn i hi d b hd hb j hj).2 he
    rw [ite_eq_right e1, ite_eq_right e2]
    exact h i hi d b hd hb
  · obtain ⟨j, hj, hk⟩ := List.mem_flatMap.mp hi
    have hj' := List.mem_range.mp hj
    simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · rw [wrArr_copyMov] at hd; cases hd
    · rw [wrArr_copyLoad] at hd; cases hd
    · rw [wrArr_copyStore] at hd
      rw [rdArr_copyStore] at hb
      cases hd
      cases hb
      rw [ite_eq_left ⟨j, hj', rfl⟩]
      split
      · rfl
      · cases j with
        | zero => rfl
        | succ j =>
          rename_i hno
          exact absurd ⟨j, by omega, rfl⟩ hno

end OwnBase

/-! ## 7. The facts of the code of one chain of stores -/

section ChainFacts

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO aliasTab)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (ReadAt WrAt rdArr wrArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webLook webRen webB stepRen)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportDefInitSort (renArr_renArr)

/-- The facts of the code the gate reads that the canonicalization of the allocation input
    needs: the class of every instruction, the agreement of the roots of every store, and no
    array of a store is a copy version. -/
def CodeFacts (C : List LinstrRM) : Prop :=
  (∀ i ∈ C, StoreClass i) ∧ AliasAgree C
    ∧ ∀ i ∈ C, ∀ d b, wrArr (fun _ => none) i = some d → rdArr (fun _ _ => none) i = [b] →
      ∀ D, '#' ∉ D.toList → ∀ k, d ≠ copyName D (k + 1) ∧ b ≠ copyName D (k + 1)

variable {nArgs : Nat} {fn : String}

/-- **The facts of the export of one chain of stores.** -/
theorem codeFacts_export {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) (hn : nArgs ≤ Γ.length) {n : Nat}
    {r : Exported} (hr : exportR nArgs fn p Γ.length n = some r)
    (hsh : ∀ i ∈ r.code, LprogIsa.shadowCall? i.1 = none) : CodeFacts r.code := by
  obtain ⟨x, -, -, hAl, hE, -⟩ := loadsChain_export_class (fn := fn) h hn hr
  obtain ⟨hR, hW, -⟩ := loadsChain_export (fn := fn) (aa := fun _ _ => none)
    (ao := fun _ => none) (fun _ _ => rfl) (fun _ => rfl) h hn hr
  refine ⟨fun i hi => ?_, ?_, fun i hi d b hd hb D hD k => ?_⟩
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    refine ⟨hsh i hi, (hE k i hk).2.2.2.1, fun d hd => ?_⟩
    obtain ⟨b, hb, hM, -⟩ := (hE k i hk).2.2.2.2 d hd
    exact ⟨b, hb, hM⟩
  · refine aliasAgree_of_root (z := x) (fun w d hw => ?_) (fun y hy => ?_)
      (fun k i d b hk hd hb => ?_)
    · show (r.code.foldl (aliasStepO []) {}).getD d d = x
      rw [(hAl {}).1 w d hw]
      simp
    · show (r.code.foldl (aliasStepO []) {}).getD y y = y
      rw [(hAl {}).2 y hy]
      simp
    · obtain ⟨b', hb', -, hx⟩ := (hE k i hk).2.2.2.2 d hd
      rw [hb] at hb'
      cases hb'
      rcases hx with rfl | ⟨k₀, -, hk₀⟩
      · exact .inr rfl
      · exact .inl ⟨k₀, hk₀⟩
  · obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hi
    refine ⟨?_, ?_⟩
    · rw [hW c d ⟨i, hc, hd⟩]
      exact ne_copyName_of_hash (hash_not_mem_regName _) _ k
    · have hbr : b ∈ rdArr (fun _ _ => none) i := by rw [hb]; exact List.mem_singleton_self _
      exact ne_copyName_of_hash (hR c b (.inl ⟨i, hc, hbr⟩)).hash_not_mem _ k

/-- **The facts of the webs of the export of one chain of stores.** -/
theorem codeFacts_webs (tab : X86Backend.ArrWebs.WebSt × Std.HashSet Nat × Std.HashSet Nat)
    {L : Nat → List String} {obsW : List String}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (h : LoadsChain p) (hn : nArgs ≤ Γ.length) {n : Nat} {r : Exported}
    (hr : exportR nArgs fn p Γ.length n = some r)
    (hsh : ∀ i ∈ r.code, LprogIsa.shadowCall? i.1 = none)
    (hacc : webB (webLook tab) r.code L obsW (fun _ _ => none) (fun _ => none) = true) :
    CodeFacts (webRen (webLook tab) (fun _ => none) r.code) := by
  obtain ⟨x, hx, hC, -, hE, -⟩ := loadsChain_export_class (fn := fn) h hn hr
  obtain ⟨hR, hW, -⟩ := loadsChain_export (fn := fn) (aa := fun _ _ => none)
    (ao := fun _ => none) (fun _ _ => rfl) (fun _ => rfl) h hn hr
  have hplain : ∀ i ∈ r.code, PlainTag i := fun i hi => by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    exact (hE k i hk).1
  have hst : ∀ (k : Nat) (i : LinstrRM), r.code[k]? = some i → StraightOp i := fun k i hk =>
    straightOp_of_lopn (hsh i (List.mem_of_getElem? hk)) (hE k i hk).2.1
  have hself : ∀ (k : Nat) (i : LinstrRM) (d : String), r.code[k]? = some i →
      wrArr (fun _ => none) i = some d → d ∉ rdArr (fun _ _ => none) i := by
    intro k i d hi hd hr'
    have h1 := hW k d ⟨i, hi, hd⟩
    exact (hR k d (.inl ⟨i, hi, hr'⟩)).ne_regName le_rfl h1
  have hhW : ∀ k d, WrAt r.code (fun _ => none) k d → '#' ∉ d.toList := fun k d hd => by
    rw [hW k d hd]
    exact hash_not_mem_regName _
  have hssa : ∀ k₁ k₂ d, WrAt r.code (fun _ => none) k₁ d →
      WrAt r.code (fun _ => none) k₂ d →
      k₁ = k₂ := fun k₁ k₂ d h₁ h₂ => by
    have := JasminLsemSimulation.regName_injective ((hW k₁ d h₁).symm.trans (hW k₂ d h₂))
    omega
  have hA1 : ∀ (k : Nat) (i : LinstrRM), r.code[k]? = some i →
      wrArr (fun _ => none) i = none →
      ∀ M ρ, aliasStepO [] M (renArr ρ i) = M := fun k i hi => (hE k i hi).2.2.2.1
  have hA2 := fun k i d hi => (hE k i hi).2.2.2.2 d
  have hal := getD_foldl_webRen tab hacc hst hplain hself hhW hssa hx hC.1 hA1 hA2
  -- the instruction at a position of the webs
  have hat : ∀ k i, (webRen (webLook tab) (fun _ => none) r.code)[k]? = some i →
      ∃ i0, r.code[k]? = some i0 ∧ i = renArr (stepRen (webLook tab) (fun _ => none) k i0) i0 :=
    fun k i hk => by
      rw [getElem?_webRen] at hk
      obtain ⟨i0, hi0, rfl⟩ := Option.map_eq_some_iff.mp hk
      exact ⟨i0, hi0, rfl⟩
  -- a store of the webs is the renamed store of the export
  have hwr : ∀ k i0 d b, r.code[k]? = some i0 →
      wrArr (fun _ => none) (renArr (stepRen (webLook tab) (fun _ => none) k i0) i0) = some d →
      rdArr (fun _ _ => none) (renArr (stepRen (webLook tab) (fun _ => none) k i0) i0) = [b] →
      ∃ d0 b0, wrArr (fun _ => none) i0 = some d0 ∧ rdArr (fun _ _ => none) i0 = [b0]
        ∧ d = webLook tab (k + 1) d0 ∧ b = webLook tab k b0 := by
    intro k i0 d b hi0 hd hb
    have hp := hplain i0 (List.mem_of_getElem? hi0)
    rw [(rdArr_wrArr_renArr _ i0 hp).2] at hd
    rw [(rdArr_wrArr_renArr _ i0 hp).1] at hb
    obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
    obtain ⟨b0, hb0, hb1⟩ := List.map_eq_singleton_iff.mp hb
    have hne : b0 ≠ d0 := by
      intro e
      refine hself k i0 d0 hi0 hd0 ?_
      rw [hb0, e]
      exact List.mem_singleton_self _
    refine ⟨d0, b0, hd0, hb0, (by simp [stepRen, hd0]), ?_⟩
    rw [← hb1]
    simp only [stepRen, hd0, Option.some.injEq]
    rw [ite_eq_right (Ne.symm hne)]
  refine ⟨fun i hi => ?_, ?_, fun i hi d b hd hb D hD k => ?_⟩
  · obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hi
    obtain ⟨i0, hi0, rfl⟩ := hat c i hc
    have hp := hplain i0 (List.mem_of_getElem? hi0)
    refine ⟨RegionCoComplete.noShadow_renArr _ (hsh i0 (List.mem_of_getElem? hi0)),
      fun hw M ρ => ?_, fun d hd => ?_⟩
    · rw [(rdArr_wrArr_renArr _ i0 hp).2] at hw
      rw [renArr_renArr]
      exact hA1 c i0 hi0 (Option.map_eq_none_iff.mp hw) M _
    · rw [(rdArr_wrArr_renArr _ i0 hp).2] at hd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hd
      obtain ⟨b0, hb0, hM, -⟩ := hA2 c i0 d0 hi0 hd0
      refine ⟨stepRen (webLook tab) (fun _ => none) c i0 b0, ?_, fun M ρ => ?_⟩
      · rw [(rdArr_wrArr_renArr _ i0 hp).1, hb0]
        rfl
      · rw [renArr_renArr, hM]
        rfl
  · refine aliasAgree_of_root (z := webLook tab 0 x) (fun w d hw => (hal d).1 w hw)
      (fun y hy => (hal y).2 hy) (fun k i d b hk hd hb => ?_)
    obtain ⟨i0, hi0, rfl⟩ := hat k i hk
    obtain ⟨d0, b0, hd0, hb0, -, rfl⟩ := hwr k i0 d b hi0 hd hb
    have hk : k < r.code.length := (List.getElem?_eq_some_iff.mp hi0).1
    have hlive : b0 ∈ L k :=
      (webB_live hacc hi0 (hst k i0 hi0).1).1 b0 (by rw [hb0]; exact List.mem_singleton_self _)
    obtain ⟨b1, hb1, -, hx'⟩ := hA2 k i0 d0 hi0 hd0
    rw [hb0] at hb1
    cases hb1
    rcases hx' with rfl | ⟨k₀, hk₀, hW₀⟩
    · right
      exact ((webB_const' hacc hst (a := 0) k (Nat.zero_le _) hk.le hlive
        (fun j i' _ _ hi' hw' => hC.1 j ⟨i', hi', hw'⟩)).2).symm
    · left
      refine ⟨k₀, ?_⟩
      have h1 := wrAt_webRen_of (w := webLook tab) hplain hW₀
      have hc := webB_const' hacc hst (a := k₀ + 1) k (by omega) hk.le hlive
        (fun j i' hj _ hi' hw' => by
          have := hssa j k₀ b0 ⟨i', hi', hw'⟩ hW₀
          omega)
      rw [hc.2] at h1
      exact h1
  · obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hi
    obtain ⟨i0, hi0, rfl⟩ := hat c i hc
    obtain ⟨d0, b0, hd0, hb0, rfl, rfl⟩ := hwr c i0 d b hi0 hd hb
    have hb0n : '#' ∉ b0.toList := by
      have hbr : b0 ∈ rdArr (fun _ _ => none) i0 := by
        rw [hb0]; exact List.mem_singleton_self _
      exact (hR c b0 (.inl ⟨i0, hi0, hbr⟩)).hash_not_mem
    exact ⟨(webLook_ne_copyName tab (hhW c d0 ⟨i0, hi0, hd0⟩) hD _ k).1,
      (webLook_ne_copyName tab hb0n hD _ k).1⟩

end ChainFacts

/-! ## 8. The head of the allocation input -/

section AllocHead

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO aliasTab)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (rdArr wrArr)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapFinal (StoreOwnBase allocCo
  resAliasTab_congr storeOwnBase_backEdgePins storeOwnBase_livepin
  canonicalizeMemrefThread_of_storeOwnBase)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapAlign (regionAllocBody)

/-- The instructions of the result copy are of the class `StoreClass`. -/
theorem storeClass_resCopyCode (src D : String) (m : Nat) :
    ∀ i ∈ resCopyCode src D m, StoreClass i := by
  intro i hi
  obtain ⟨j, -, hk⟩ := List.mem_flatMap.mp hi
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · refine ⟨rfl, fun _ M ρ => ?_, fun d hd => by cases hd⟩
    simp [renArr, aliasStepO, ExportRegions.movImmI, ExportRegions.movI, LprogIsa.shadowCall?,
      withWidthTag, X86Backend.ImageCoalesceCfg.renCallW]
  · refine ⟨rfl, fun _ M ρ => ?_, fun d hd => by cases hd⟩
    have hl : isMemStore "LOADIDX" = false := by decide
    simp [renArr, aliasStepO, X86Backend.ImageCoalesceCfg.renLoad, LprogIsa.shadowCall?, hl]
  · refine ⟨rfl, fun hd => ?_, fun d hd => ?_⟩
    · rw [wrArr_copyStore] at hd
      cases hd
    rw [wrArr_copyStore] at hd
    cases hd
    refine ⟨copyName D j, rfl, fun M ρ => ?_⟩
    simp [renArr, aliasStepO, X86Backend.ImageCoalesceCfg.renStore, LprogIsa.shadowCall?,
      isMemStore, stripWidthTag]

/-- **The stores of the coalesced code given to the allocation write their own base** when the
    code has the facts `CodeFacts` and the result buffer has no `#`. -/
theorem storeOwnBase_allocCo {a : AbiNames} {t : JasminTy} {code : List LinstrRM}
    {res : List LOperand} (hF : CodeFacts code) (hD : '#' ∉ a.outArg.toList) :
    ∀ i ∈ allocCo a t code res, StoreOwnBase i.1 := by
  obtain ⟨hcls, hag, hcp⟩ := hF
  have hC : (∀ i ∈ code ++ regionLprogCopy a none [t] code res, StoreClass i)
      ∧ AliasAgree (code ++ regionLprogCopy a none [t] code res) := by
    unfold regionLprogCopy
    dsimp only
    split
    · rename_i src D m hc
      obtain rfl := RegionAllocMapPins.resCopyOf_buf hc
      refine ⟨fun i hi => ?_, aliasAgree_append_copy hag fun i hi d b hd hb k _ =>
        hcp i hi d b hd hb _ hD k⟩
      rcases List.mem_append.mp hi with hi | hi
      · exact hcls i hi
      · exact storeClass_resCopyCode src _ m i hi
    · simp only [List.append_nil]
      exact ⟨hcls, hag⟩
  intro i hi
  obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
  exact storeOwnBase_of_class (hC.1 i' hi') fun d b hd hb =>
    resAliasTab_congr _ (hC.2 i' hi' d b hd hb)

/-- **The head of the allocation input** of a region export with fewer than four parameters,
    when the stores of its coalesced code write their own base and the entry names hold the
    argument names below `nArgs > 0`: a liveness instruction reading the argument names. -/
theorem regionAllocBody_pin {a : AbiNames} {nArgs : Nat} {t : JasminTy} {r : Exported}
    (hlt : a.abiArgs.length < 4) (hpos : 0 < nArgs)
    (hown : ∀ i ∈ allocCo a t r.code r.res, StoreOwnBase i.1)
    (hne : ∀ j, j < nArgs → argName j ∈ entryPinNames a
      (regionAllocCode (r.code ++ regionLprogCopy a none [t] r.code r.res)
        [] (resAliasOf none (some a.outArg) [t] r.res))) :
    ∃ ns : List String, (regionAllocBody a nArgs [t] r)[0]? = some ⟨0, .Lopn [.reg "%livepin"]
      "LIVEPIN" (ns.map LOperand.reg)⟩ ∧ ∀ j, j < nArgs → argName j ∈ ns := by
  unfold regionAllocBody
  dsimp only
  split
  · refine ⟨(List.range nArgs).map argName, ?_, fun j hj =>
      List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩
    simp [List.map_map, Function.comp_def]
  · refine ⟨_, ?_, hne⟩
    have hne' : entryPinNames a (regionAllocCode (r.code ++ regionLprogCopy a none [t] r.code
        r.res) [] (resAliasOf none (some a.outArg) [t] r.res)) ≠ [] := by
      intro he
      have := hne 0 hpos
      rw [he] at this
      cases this
    rw [ite_eq_right (by omega), List.nil_append, canonicalizeMemrefThread_of_storeOwnBase]
    · unfold arrBasePins
      dsimp only
      rw [ite_eq_right (by simpa using hne')]
      rfl
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · unfold arrBasePins at hi
        dsimp only at hi
        split at hi
        · cases hi
        · rw [List.mem_singleton.mp hi]
          exact storeOwnBase_livepin _ _
      · rcases List.mem_append.mp hi with hi | hi
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
          exact storeOwnBase_backEdgePins hown j hj
        · rw [List.mem_singleton.mp hi]
          intro dst opn base x s rest he
          cases he

end AllocHead

/-! ## 9. The stage `G4` on the field domain -/

section Field

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO aliasTab
  aliasTabRes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapAlign (regionAllocBody regionAllocTbl
  regionLprogC_cert)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapComplete (renOf_filter_allocCertOf
  physRegName_cases)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapPins (liveAt_of_touchW TouchW)
open CatCrypt.Crypto.Hax (HaxModule)

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **The layout of a member of the field domain**: `k ∈ {1, 2}` operands and the output
    array, each of `n` words, and the result the `n` words at `%rdi`. -/
theorem fieldDomB_layout (h : fieldDomB e σ = true) :
    ∃ k n, (k = 1 ∨ k = 2) ∧ σ.args = (FieldRoute.fieldAbi k n).args
      ∧ σ.result = .words "%rdi" n := by
  unfold fieldDomB at h
  split at h
  · rename_i k n hE
    obtain ⟨m, p, hm, -⟩ := fieldDomE_wide hE
    simp only [fieldAbiB, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨k, n, ?_, h.1.1.1.1.1, ?_⟩
    · simp only [fieldMethods, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      omega
    · have hr := h.1.1.1.2
      cases hres : σ.result <;> simp_all [resultWords?]
  · cases h

/-- **Every argument name of a member of the field domain is read by the liveness instruction
    at entry**, and the layout has fewer than four parameters. -/
theorem fieldDom_entryPin (h : fieldDomB e σ = true) (fname : String) (C : List LinstrRM) :
    (nfAbiNames fname σ).abiArgs.length < 4
      ∧ ∀ j, j < σ.args.length → argName j ∈ entryPinNames (nfAbiNames fname σ) C := by
  obtain ⟨k, n, hk, ha, hr⟩ := fieldDomB_layout h
  refine ⟨?_, fun j hj => ?_⟩
  · simp only [nfAbiNames, ha, FieldRoute.fieldAbi, List.length_map, List.length_range]
    omega
  · rw [ha] at hj
    simp only [FieldRoute.fieldAbi, List.length_map, List.length_range] at hj
    unfold entryPinNames
    simp only [nfAbiNames, nfOutIdx, ha, hr]
    rcases hk with rfl | rfl <;> interval_cases j <;>
      simp [FieldRoute.fieldAbi, FieldRoute.fieldArgReg, argBasePairsPos, List.range_succ,
        List.zipIdx, List.zipIdx_cons, argName, FieldRoute.fieldArgName]

/-- The gate does not refuse at `renB` when the renaming check accepts. -/
theorem regionCoStage_ne_renB {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String}
    (h : renB σ nm [] (regionCoBody σ nm t (calleeCodeT none code) res none)
      (regionCoParts σ nm b t (calleeCodeT none code) res cert none).ps = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "renB" := by
  unfold regionCoStage
  dsimp only
  rw [h]
  simp only [Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- The image of a name under the allocation of a body without a call is a physical name. -/
theorem physName_allocName {B : Lcmd} {tbl : Array Nat} (hc : bodyHasCall B = false)
    (n : String) : PhysName (allocName B tbl n) := by
  unfold allocName
  rw [hc, ite_eq_right Bool.false_ne_true]
  exact physRegName_cases _

/-- **Stage `G4` on the field domain**: the gate does not refuse at the renaming check
    `renB`. -/
theorem fieldDom_renB (h : fieldDomB e σ = true) (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "renB" := by
  refine regionCoStage_ne_renB ?_
  obtain ⟨t0, q, q', r0, P, hq, hq', hr0, hr, hP, -, rfl⟩ := hB
  have hL := fieldDom_legalize_loadsChain h hq hq'
  have hret : ∀ res, regionRet σ exportReg (NarrowWords.wideTy t0) res = none := by
    obtain ⟨-, R, n, hR⟩ := fieldDomB_abi h
    exact fun _ => regionRet_words hR
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
  have hF : CodeFacts r.code := by
    rcases regionWebsAt_cases (regionWebsEx σ exportReg) r0 with he | ⟨tab, L, hacc, he⟩
    · rw [hr, he]
      exact codeFacts_export hL le_rfl hr0 hsh
    · rw [hr, he]
      exact codeFacts_webs tab hL le_rfl hr0 hsh hacc
  have hX : RegionExp fname (legalizeRegion q') (regionWebsEx σ exportReg) r := by
    rw [hr]
    exact regionExp_webs _ hr0
  obtain ⟨r1, r2, hr1, hr2, hcert⟩ := regionLprogC_cert (nfAbiNames fname σ) _ _ hP
  obtain rfl : r1 = r0 := Option.some.inj (hr1.symm.trans hr0)
  rw [← hr] at hr2
  subst r2
  subst hcert
  have hshape : ∀ i ∈ r.code, RegionAllocMapDom.ShapeB i.1 := fun i hi =>
    (hX.mnemDom hEx hcf i hi).2.2
  have hBs := RegionAllocMapDom.shapeB_regionAllocBody (nfAbiNames fname σ)
    ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r hshape
  have hc := RegionAllocMapDom.bodyHasCall_of_shapeB hBs
  have hv : ∀ s, slotIsVec (bodyVecSlots (regionAllocBody (nfAbiNames fname σ)
      ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)) s = false := by
    intro s
    rw [RegionAllocMapDom.bodyVecSlots_of_shapeB hBs]
    simp only [slotIsVec, Array.getElem?_replicate]
    split <;> rfl
  have hlenA : ((nfCtx σ).map NarrowWords.wideTy).length = σ.args.length := by
    rw [List.length_map, RegionAllocMapDom.nfCtx_length]
  obtain ⟨hlt, hpin⟩ := fieldDom_entryPin h fname
    (regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none
      [NarrowWords.wideTy t0] r.code r.res) [] (resAliasOf none
        (some (nfAbiNames fname σ).outArg) [NarrowWords.wideTy t0] r.res))
  have hpos : 0 < σ.args.length := by
    obtain ⟨k, n, -, ha, -⟩ := fieldDomB_layout h
    rw [ha]
    simp [FieldRoute.fieldAbi]
  have hD : '#' ∉ (nfAbiNames fname σ).outArg.toList := by
    show '#' ∉ (((nfOutIdx σ).map argName).getD "").toList
    cases nfOutIdx σ with
    | none => simp
    | some j => exact hash_not_mem_argName j
  obtain ⟨ns, hB0, hns⟩ := regionAllocBody_pin (nArgs := ((nfCtx σ).map NarrowWords.wideTy).length)
    hlt (hlenA ▸ hpos) (storeOwnBase_allocCo hF hD) (fun j hj => hpin j (hlenA ▸ hj))
  -- the allocation separates the argument names
  have hinj : ∀ n₁ ∈ allocCertNames (regionAllocBody (nfAbiNames fname σ)
        ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r),
      ∀ n₂ ∈ allocCertNames (regionAllocBody (nfAbiNames fname σ)
        ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r),
      isArgNameB σ n₁ = true → isArgNameB σ n₂ = true →
      allocName (regionAllocBody (nfAbiNames fname σ)
          ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)
        (regionAllocTbl [NarrowWords.wideTy t0] (regionAllocBody (nfAbiNames fname σ)
          ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)) n₁
      = allocName (regionAllocBody (nfAbiNames fname σ)
          ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)
        (regionAllocTbl [NarrowWords.wideTy t0] (regionAllocBody (nfAbiNames fname σ)
          ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)) n₂ →
      n₁ = n₂ := by
    intro n₁ h₁ n₂ h₂ ha₁ ha₂ he
    by_contra hne
    obtain ⟨j₁, hj₁, rfl⟩ := RegionAllocMapLive.exists_of_isArgNameB ha₁
    obtain ⟨j₂, hj₂, rfl⟩ := RegionAllocMapLive.exists_of_isArgNameB ha₂
    have ht : ∀ j, j < σ.args.length → TouchW (argName j)
        (Linstr.li_i ⟨0, .Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg)⟩) :=
      fun j hj => ⟨_, _, _, rfl, Or.inr (by
        simpa [List.flatMap_map, LOperand.srcRegNames] using hns j (hlenA ▸ hj))⟩
    obtain ⟨pos, hl₁, hl₂⟩ := liveAt_of_touchW hB0 (ht j₁ hj₁) hB0 (ht j₂ hj₂) hB0 (ht j₁ hj₁)
      le_rfl le_rfl
    exact allocName_ne_of_liveAt_noVec hc hv (List.mem_filter.mp h₁).1
      (List.mem_filter.mp h₂).1 hne hl₁ hl₂ he
  have hpairs : ∀ p ∈ certArgs σ (allocCertOf (regionAllocBody (nfAbiNames fname σ)
        ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)
        (regionAllocTbl [NarrowWords.wideTy t0] (regionAllocBody (nfAbiNames fname σ)
          ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r))),
      p.1 ∈ allocCertNames (regionAllocBody (nfAbiNames fname σ)
        ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)
      ∧ isArgNameB σ p.1 = true
      ∧ p.2 = allocName (regionAllocBody (nfAbiNames fname σ)
          ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)
        (regionAllocTbl [NarrowWords.wideTy t0] (regionAllocBody (nfAbiNames fname σ)
          ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)) p.1 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
    obtain ⟨n, m⟩ := p
    obtain ⟨hn, rfl⟩ := mem_allocCertOf.mp hp1
    exact ⟨hn, hp2, rfl⟩
  have hphys : ∀ p ∈ certArgs σ (allocCertOf (regionAllocBody (nfAbiNames fname σ)
        ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)
        (regionAllocTbl [NarrowWords.wideTy t0] (regionAllocBody (nfAbiNames fname σ)
          ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r))),
      PhysName p.2 ∧ ∃ j, j < σ.args.length ∧ p.1 = argName j := by
    intro p hp
    obtain ⟨-, ha, he⟩ := hpairs p hp
    rw [he]
    obtain ⟨j, hj, hj'⟩ := RegionAllocMapLive.exists_of_isArgNameB ha
    exact ⟨physName_allocName hc _, j, hj, hj'⟩
  -- the names of the coalesced code
  have hsym : ∀ i ∈ r.code, RegionExportDefInit.symReads i = [] := fun i hi =>
    (hX.mnemDom hEx hcf i hi).1
  have hlen : ((nfCtx σ).map NarrowWords.wideTy).length ≤ σ.args.length := hlenA.le
  have hCn := codeName_regionCoCode fname (legalizeRegion q') hEx hcf hX σ exportReg
    (NarrowWords.wideTy t0) hsym hlen (hret r.res)
  have hCs := RegionCoComplete.noShadow_regionCoCode σ exportReg (NarrowWords.wideTy t0) r.code
    r.res (regionCopy σ exportReg (NarrowWords.wideTy t0) none r.code r.res)
    (hX.noShadow hEx hcf)
  have hρ : ∀ x, CodeName x → CodeName (canonMemrefName (regionAliasTab σ exportReg
      (NarrowWords.wideTy t0) none r.res (regionCoCode σ exportReg (NarrowWords.wideTy t0) r.code
        r.res (regionCopy σ exportReg (NarrowWords.wideTy t0) none r.code r.res))) x) := by
    intro x hx
    unfold regionAliasTab resAliasTab
    split
    · rename_i D src hrr
      have hDn : CodeName D := by
        have hD0 : (regionResBuf σ exportReg).map Prod.fst = some D := by
          unfold resAliasOf at hrr
          split at hrr
          · split at hrr
            · cases hrr
            · cases hrr
              assumption
          · cases hrr
        obtain ⟨⟨D1, n1⟩, hb, rfl⟩ := Option.map_eq_some_iff.mp hD0
        unfold regionResBuf at hb
        split at hb
        · obtain ⟨j, -, -, -, rfl, -⟩ := X86Backend.ImageAddrRoute.slotArrOf_some hb
          exact codeName_argName j
        · cases hb
      unfold aliasTabRes
      split
      · refine alias_foldl_pred [] _ _ hCn hCs (fun y hy => ?_) x hx
        unfold canonMemrefName
        rw [Std.HashMap.getD_insert]
        split
        · simpa using hDn
        · simpa using hy
      · exact alias_foldl_pred [] _ {} hCn hCs (fun y hy => by simpa [canonMemrefName] using hy) x hx
    · exact alias_foldl_pred [] _ {} hCn hCs (fun y hy => by simpa [canonMemrefName] using hy) x hx
  have hnames : ∀ x ∈ loopNames (regionCoBody σ exportReg (NarrowWords.wideTy t0)
      (calleeCodeT none r.code) r.res none), x = "" ∨ CodeName x := by
    intro x hx
    simp only [loopNames, List.mem_cons, List.mem_flatMap] at hx
    rcases hx with hx | ⟨i, hi, hx⟩
    · exact .inl hx
    · right
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
      rcases under_renArr _ (hCs i0 hi0) x hx with hx | ⟨y, hy, rfl⟩
      · exact hCn i0 hi0 x hx
      · exact hρ y (hCn i0 hi0 y hy)
  refine renB_intro (fun i hi => ?_) ?_ (fun p hp q hq => ?_) (fun p hp => ?_) (fun p hp hm => ?_)
    (fun p hp => ?_) ?_ (fun j hj p hp => ?_)
  · have hFB : ∀ i ∈ regionCoBody σ exportReg (NarrowWords.wideTy t0) (calleeCodeT none r.code)
        r.res none, RegionExportForms.FormB i := by
      intro i hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
      exact RegionExportForms.formB_renArr _ (RegionExportForms.formB_regionCoCode (r := r)
        (by rw [hr]; exact RegionExportForms.formB_regionWebsAt hr0 _ none) σ exportReg
        (NarrowWords.wideTy t0) _ i0 hi0)
    have := RegionExportForms.clsB_mulxFree_of_formB (hFB i hi)
    simp [this.1, this.2]
  · have hl : certArgs σ (allocCertOf (regionAllocBody (nfAbiNames fname σ)
          ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)
          (regionAllocTbl [NarrowWords.wideTy t0] (regionAllocBody (nfAbiNames fname σ)
            ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)))
        = ((allocCertNames (regionAllocBody (nfAbiNames fname σ)
          ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)).filter
            (isArgNameB σ)).map fun n => (n, allocName (regionAllocBody (nfAbiNames fname σ)
              ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)
              (regionAllocTbl [NarrowWords.wideTy t0] (regionAllocBody (nfAbiNames fname σ)
                ((nfCtx σ).map NarrowWords.wideTy).length [NarrowWords.wideTy t0] r)) n) := by
      unfold certArgs allocCertOf
      rw [List.filter_map]
      rfl
    show (List.map Prod.snd (certArgs σ _)).Nodup
    rw [hl, List.map_map]
    refine List.Nodup.map_on (fun x hx y hy he => hinj x (List.mem_filter.mp hx).1 y
      (List.mem_filter.mp hy).1 (List.mem_filter.mp hx).2 (List.mem_filter.mp hy).2 he) ?_
    exact ((RegionCoComplete.nodup_eraseDups _).filter _).filter _
  · obtain ⟨hq2, -⟩ := hphys q hq
    obtain ⟨-, j, -, hj⟩ := hphys p hp
    rw [hj]
    exact fun he => hq2.not_codeName (he ▸ codeName_argName j)
  · obtain ⟨h1, h2, h3⟩ := hpairs p hp
    show renOf (certArgs σ _) p.1 = p.2
    unfold certArgs
    rw [renOf_filter_allocCertOf, ite_eq_left ⟨h1, h2⟩, h3]
  · obtain ⟨hp2, -⟩ := hphys p hp
    rcases hnames _ hm with h0 | h0
    · exact hp2.ne_empty h0
    · exact hp2.not_codeName h0
  · obtain ⟨-, j, -, hj⟩ := hphys p hp
    rw [hj]
    exact RegionAllocMapDom.argName_ne_empty j
  · simp [argBind, JasminLsemRenameLoop.movesOf, noStoreB]
  · obtain ⟨hp2, -⟩ := hphys p hp
    exact fun he => hp2.not_codeName (he ▸ codeName_argName j)

example (S : FieldDomStages) : type_of% @S.renB :=
  fun h hB => fieldDom_renB (fieldDomB_of_fieldDomB' h) hB

end Field

/-! ## 10. The stage `G6` on the field domain -/

section ResultCopy

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **Stage `G6` on the field domain**: the gate does not refuse at the result copy names
    `coResultCopy`, since the layout has no register result and so no result copy. -/
theorem fieldDom_coResultCopy (h : fieldDomB e σ = true) (_hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coResultCopy" := by
  have hret : regionRet σ exportReg t r.res = none := by
    obtain ⟨-, R, n, hR⟩ := fieldDomB_abi h
    exact regionRet_words hR
  unfold regionCoStage
  dsimp only
  rw [hret]
  simp only [Option.toList_none, List.all_nil, Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

example (S : FieldDomStages) : type_of% @S.coResultCopy :=
  fun h hB => fieldDom_coResultCopy (fieldDomB_of_fieldDomB' h) hB

end ResultCopy

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
