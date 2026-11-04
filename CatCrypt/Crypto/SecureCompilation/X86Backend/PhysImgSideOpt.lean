/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgOpt

/-!
# The optimiser side conditions on the looped physical ABI export

The side condition `PhysImgOpt.optSideB` of a modeled run of the basic-block optimiser is the
conjunction of the side conditions of `elimReloads` (`elimSideB`), of `reloadElimBody`
(`reloadPairSideB`) and of `loadCSE` (`loadSideB`). This module proves the order conditions of
`elimSideB` and the condition `reloadPairSideB` on every straight run of a sublist of the fused
export body, so that `optSideB` on a modeled run follows from `loadSideB` on it.

A spill pair `MOV q ← r; MOV r ← q` into an array slot `q` needs a write of `q`, and the export
writes an array slot only in the saves `MOVQ qsave.R, R` of the prologue (`StoreSelf`). No
instruction of the fused body moves `qsave.R` back into `R` when `qsave.R` is an array slot
(`LoadOk`): the argument materialization moves a save slot into another register or `R15`,
an expansion reads a save slot only into `R14`, and the slots of the callee-saved registers
are no array slots.

The export body of `lfundefPhysAbiOfVirtCert` is the prologue, which writes the array slots
and reads no array slot, followed by instructions none of which writes an array slot. The
fusion keeps this order: it passes every instruction but a fusion site, and a site and every
instruction behind it write no array slot (`fuse_step`). The condition that no array slot is
written behind a reload from an array slot (`slotAfterSlotReloadFreeB`) and the condition that
a reload into an array slot reads no array slot (`saveSrcB`) are closed under sublists, so they
hold on every run of every sublist of the fused body.

## Main results

* `slotAfterSlotReloadFreeB_sublist`, `saveSrcB_sublist`: the two order conditions on
  sublists.
* `fuse_mem`, `fuse_slotAfter`: every instruction of the fusion is an instruction of the body
  or writes no array slot, and the fusion keeps `slotAfterSlotReloadFreeB`.
* `order_lfundefPhysAbiOfVirtCert`: the two order conditions on the fused export body.
* `elimSideB_of_run`: `elimSideB` on every modeled run of a sublist of the fused body.
* `physExpand_forall`: a property of every operation whose sources name no array slot and of
  the memref base reload holds of every instruction of an expansion.
* `reloadPairSideB_of_pairs`, `reloadPairSideB_of_run`, `pairs_lfundefPhysAbiOfVirtCert`:
  `reloadPairSideB` from the spill-pair conditions `StoreSelf` and `LoadOk`, which hold on
  the fused export body.
* `optSideB_of_loadSide`, `optSideB_runs`: `optSideB` from its three parts, on every run.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideOpt

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (bodyAllModeled
  splitStraightRuns splitStraightRuns_flatten)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFuse
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
  (physExpand physExpand_eq physRmap notLivePin)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgOpt
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass (gpNameB_of_isSlotName)

variable {slotArr : String → Option (String × Nat)}

/-! ## 1. The order conditions on lists -/

/-- The instruction writes no array slot. -/
def noSlotWriteB (slotArr : String → Option (String × Nat)) (j : Linstr) : Bool :=
  (writtenNames j.li_i).all fun q => (slotArr q).isNone

/-- A body that writes no array slot satisfies `slotAfterSlotReloadFreeB` from either flag. -/
theorem slotAfter_of_noWrite :
    ∀ (seen : Bool) (l : Lcmd), (∀ j ∈ l, noSlotWriteB slotArr j = true) →
      slotAfterSlotReloadFreeB slotArr seen l = true
  | _, [], _ => rfl
  | seen, i :: is, h => by
    have hi : noSlotWriteB slotArr i = true := h i List.mem_cons_self
    simp only [noSlotWriteB] at hi
    simp only [slotAfterSlotReloadFreeB, hi, Bool.or_true, Bool.true_and]
    exact slotAfter_of_noWrite _ is fun j hj => h j (List.mem_cons_of_mem _ hj)

/-- **`slotAfterSlotReloadFreeB` on sublists**, from a flag that is set at most when the flag
    of the body is set. -/
theorem slotAfterSlotReloadFreeB_sublist {l' l : Lcmd} (hs : l'.Sublist l) :
    ∀ {s' s : Bool}, (s' = true → s = true) → slotAfterSlotReloadFreeB slotArr s l = true →
      slotAfterSlotReloadFreeB slotArr s' l' = true := by
  induction hs with
  | slnil => intros; rfl
  | cons a _ ih =>
    intro s' s hss h
    simp only [slotAfterSlotReloadFreeB, Bool.and_eq_true] at h
    exact ih (fun h' => by simp [hss h']) h.2
  | cons_cons a _ ih =>
    intro s' s hss h
    simp only [slotAfterSlotReloadFreeB, Bool.and_eq_true] at h ⊢
    refine ⟨?_, ih (fun h' => ?_) h.2⟩
    · cases s' with
      | false => rfl
      | true => simpa [hss rfl] using h.1
    · simp only [Bool.or_eq_true] at h' ⊢
      exact h'.imp hss id

/-- The reload condition of `saveSrcB` at one instruction. -/
def saveSrcI (slotArr : String → Option (String × Nat)) (j : Linstr) : Bool :=
  match asReload j.li_i with
  | some (d, s) => (slotArr d).isNone || (slotArr s).isNone
  | none => true

theorem saveSrcB_iff {b : Lcmd} : saveSrcB slotArr b = true ↔ ∀ j ∈ b, saveSrcI slotArr j = true :=
  List.all_eq_true

/-- **`saveSrcB` on sublists.** -/
theorem saveSrcB_sublist {l' l : Lcmd} (hs : l'.Sublist l) (h : saveSrcB slotArr l = true) :
    saveSrcB slotArr l' = true :=
  saveSrcB_iff.mpr fun j hj => saveSrcB_iff.mp h j (hs.subset hj)

theorem asReload_eq {r : LinstrR} {d s : String} (h : asReload r = some (d, s)) :
    ∃ o, r = .Lopn [.reg d] o [.reg s] := by
  unfold asReload at h
  split at h
  · split at h
    · cases h; exact ⟨_, rfl⟩
    · cases h
  · cases h

/-- An instruction that writes no array slot reloads into no array slot. -/
theorem saveSrcI_of_noWrite {j : Linstr} (h : noSlotWriteB slotArr j = true) :
    saveSrcI slotArr j = true := by
  unfold saveSrcI
  split
  · rename_i d s hr
    obtain ⟨o, ho⟩ := asReload_eq hr
    simp [noSlotWriteB, ho, writtenNames] at h
    simp [h]
  · rfl

/-- An instruction whose destinations are no array slots writes no array slot. -/
theorem noWrite_of_dstOkB {j : Linstr} (h : dstOkB slotArr j.li_i = true) :
    noSlotWriteB slotArr j = true := by
  unfold noSlotWriteB
  cases hj : j.li_i with
  | Lopn ds o ss =>
    rw [hj] at h
    simp only [dstOkB, List.all_eq_true] at h
    simp only [writtenNames, List.all_eq_true, List.mem_filterMap]
    rintro q ⟨x, hx, hxq⟩
    cases x with
    | reg n =>
      cases hxq
      simpa [operandOkB] using h _ hx
    | _ => cases hxq
  | _ => rfl

/-! ## 2. The fusion -/

/-- **One step of the fusion keeps its invariants**: the site and home conditions, the
    agreement of the environments, the scratch environment and the pending homes outside the
    array slots. The step writes the instruction itself, or a site whose instructions, and
    the instructions of the rest of the body, have no array-slot destination. -/
theorem fuse_step (s : Bool) (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    (i : Linstr) (rest : Lcmd) (ef ep : ScratchEnv) (pend : List (String × String))
    (hs : fuseSiteOkB slotArr (i :: rest) = true) (hh : homeOkB slotArr ep (i :: rest) = true)
    (hag : EnvAgree ef ep) (hes : EnvScratch ef) (hp : ∀ p ∈ pend, slotArr p.1 = none) :
    ∃ L ef' pend', fuseMulHiAux s ef pend (i :: rest) = L ++ fuseMulHiAux s ef' pend' rest ∧
      fuseSiteOkB slotArr rest = true ∧ homeOkB slotArr (scratchStep ep i) rest = true ∧
      EnvAgree ef' (scratchStep ep i) ∧ EnvScratch ef' ∧ (∀ p ∈ pend', slotArr p.1 = none) ∧
      (L = [i] ∨ ((∀ r ∈ L, dstOkB slotArr r.li_i = true) ∧
        ∀ r ∈ rest, dstOkB slotArr r.li_i = true)) := by
  obtain ⟨L, env', pend', he, ⟨ks, rfl⟩, hcase⟩ := fuseMulHiAux_cons_step s ef pend i rest
  simp only [fuseSiteOkB, homeOkB, Bool.and_eq_true] at hs hh
  have hag' := (hag.step i).killAll (hes.step i) ks
  have hes' := (hes.step i).killAll ks
  rcases hcase with ⟨rfl, hpd⟩ | ⟨d, opn, s1, s2, heq, hhi, hsub, lo, k, hlo, hout⟩
  · refine ⟨[i], _, pend', he, hs.2, hh.2, hag', hes', ?_, Or.inl rfl⟩
    rcases hpd with rfl | ⟨d, opn, s1, s2, heq, hlow, rfl⟩
    · exact hp
    · have h1 := hh.1
      rw [heq] at h1
      simp only [hlow, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        Option.isNone_iff_eq_none] at h1
      intro p hp'
      simp only [List.mem_cons] at hp'
      rcases hp' with rfl | hp'
      · cases s
        · exact h1.1
        · simp only [ite_true, lowHome]
          split
          · rcases hag d with he' | he'
            · rw [he']; exact h1.2
            · exact slotArr_scratch hq (Or.inl he')
          · exact h1.1
      · exact hp p hp'
  · have hsite : mulHiSiteB i = true := by simp [mulHiSiteB, heq, hhi]
    have h1 := hs.1
    simp only [hsite, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h1
    obtain ⟨⟨hdi, hrest⟩, -⟩ := h1
    have hd : slotArr d = none := by
      rw [heq] at hdi
      simpa [dstOkB, operandOkB] using hdi
    have hlo' : slotArr lo = none := hp (lo, k) hlo
    refine ⟨L, _, pend', he, hs.2, hh.2, hag', hes', fun p hp' => hp p (hsub p hp'),
      Or.inr ⟨fun r hr => ?_, fun r hr => List.all_eq_true.mp hrest r hr⟩⟩
    obtain ⟨-, -, hds⟩ := hout r hr
    cases hr' : r.li_i with
    | Lopn ds o ss =>
      simp only [dstOkB, List.all_eq_true]
      intro x hx
      obtain ⟨n, rfl, hn⟩ := hds ds o ss hr' x hx
      have : slotArr n = none := by
        rcases hn with hn | hn | rfl | rfl
        · exact slotArr_scratch hq (Or.inl hn)
        · exact slotArr_scratch hq (Or.inr hn)
        · exact hd
        · exact hlo'
      simp [operandOkB, this]
    | _ => rfl

/-- **Every instruction of the fusion** is an instruction of the body or has no array-slot
    destination, under the invariants of `fuse_step`. -/
theorem fuse_mem (s : Bool) (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    ∀ (rest : Lcmd) (ef ep : ScratchEnv) (pend : List (String × String)),
      fuseSiteOkB slotArr rest = true → homeOkB slotArr ep rest = true → EnvAgree ef ep →
      EnvScratch ef → (∀ p ∈ pend, slotArr p.1 = none) →
      ∀ r ∈ fuseMulHiAux s ef pend rest, r ∈ rest ∨ dstOkB slotArr r.li_i = true
  | [], _, _, _, _, _, _, _, _, r, hr => by rw [fuseMulHiAux_nil] at hr; cases hr
  | i :: rest, ef, ep, pend, hs, hh, hag, hes, hp, r, hr => by
    obtain ⟨L, ef', pend', he, hs', hh', hag', hes', hp', hc⟩ :=
      fuse_step s hq i rest ef ep pend hs hh hag hes hp
    rw [he, List.mem_append] at hr
    rcases hr with hr | hr
    · rcases hc with rfl | ⟨hL, -⟩
      · exact Or.inl (by simp only [List.mem_singleton] at hr; simp [hr])
      · exact Or.inr (hL r hr)
    · exact (fuse_mem s hq rest ef' _ pend' hs' hh' hag' hes' hp' r hr).imp
        (List.mem_cons_of_mem _) id

/-- **The fusion keeps `slotAfterSlotReloadFreeB`**, under the invariants of `fuse_step`. -/
theorem fuse_slotAfter (s : Bool)
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    ∀ (rest : Lcmd) (ef ep : ScratchEnv) (pend : List (String × String)) (seen : Bool),
      fuseSiteOkB slotArr rest = true → homeOkB slotArr ep rest = true → EnvAgree ef ep →
      EnvScratch ef → (∀ p ∈ pend, slotArr p.1 = none) →
      slotAfterSlotReloadFreeB slotArr seen rest = true →
      slotAfterSlotReloadFreeB slotArr seen (fuseMulHiAux s ef pend rest) = true
  | [], _, _, _, _, _, _, _, _, _, _ => by rw [fuseMulHiAux_nil]; rfl
  | i :: rest, ef, ep, pend, seen, hs, hh, hag, hes, hp, hsa => by
    obtain ⟨L, ef', pend', he, hs', hh', hag', hes', hp', hc⟩ :=
      fuse_step s hq i rest ef ep pend hs hh hag hes hp
    rw [he]
    rcases hc with rfl | ⟨hL, hR⟩
    · simp only [slotAfterSlotReloadFreeB, List.singleton_append, Bool.and_eq_true] at hsa ⊢
      exact ⟨hsa.1, fuse_slotAfter s hq rest ef' _ pend' _ hs' hh' hag' hes' hp' hsa.2⟩
    · refine slotAfter_of_noWrite _ _ fun j hj => ?_
      rcases List.mem_append.mp hj with hj | hj
      · exact noWrite_of_dstOkB (hL j hj)
      · rcases fuse_mem s hq rest ef' _ pend' hs' hh' hag' hes' hp' j hj with hj | hj
        · exact noWrite_of_dstOkB (hR j hj)
        · exact noWrite_of_dstOkB hj

/-! ## 3. The export -/

/-- The source of a reload has no `qsave.` prefix. -/
def srcPlainB (j : Linstr) : Bool :=
  match asReload j.li_i with
  | some (_, s) => !hasPrefix s "qsave."
  | none => true

theorem buildPrologue_srcPlain (virt : Lfundef) (tbl : Array Nat) :
    ∀ j ∈ buildPrologue virt tbl (fun _ => none), srcPlainB j = true := by
  have hP : buildPrologue virt tbl (fun _ => none) = buildPrologue {} #[] (fun _ => none) := rfl
  have c : (buildPrologue {} #[] (fun _ => none)).all srcPlainB = true := by decide +kernel
  rw [hP]
  exact List.all_eq_true.mp c

theorem extraSaves_srcPlain (abiArgs : List String) :
    ∀ j ∈ extraSaves abiArgs, srcPlainB j = true := by
  intro j hj
  obtain ⟨r, s, hs, rfl⟩ := mem_extraSaves hj
  obtain ⟨rfl, hr⟩ := abiSaveOfExt_spec hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- A reload from a source without `qsave.` prefix is no reload from an array slot and
    satisfies the reload condition of `saveSrcB`. -/
theorem srcPlain_facts (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {j : Linstr} (h : srcPlainB j = true) :
    slotSrcReloadB slotArr j = false ∧ saveSrcI slotArr j = true := by
  unfold srcPlainB at h
  unfold slotSrcReloadB saveSrcI
  cases hr : asReload j.li_i with
  | none => exact ⟨rfl, rfl⟩
  | some p =>
    obtain ⟨d, s⟩ := p
    rw [hr] at h
    have hs : slotArr s = none := slotArr_none_of_prefix hq (by simpa using h)
    simp [hs]

/-- The order condition on a body made of a prefix `A` with no reload from an array slot and a
    rest `X` that writes no array slot. -/
theorem slotAfter_append :
    ∀ (A : Lcmd) {X : Lcmd}, (∀ j ∈ A, slotSrcReloadB slotArr j = false) →
      (∀ j ∈ X, noSlotWriteB slotArr j = true) →
      slotAfterSlotReloadFreeB slotArr false (A ++ X) = true
  | [], X, _, hX => slotAfter_of_noWrite false X hX
  | i :: A, X, hA, hX => by
    simp only [List.cons_append, slotAfterSlotReloadFreeB, Bool.not_false, Bool.true_or,
      Bool.true_and, Bool.false_or, hA i List.mem_cons_self]
    exact slotAfter_append A (fun j hj => hA j (List.mem_cons_of_mem _ hj)) hX

/-- **The two order conditions on the shape of the export**: a prologue `A` whose reloads
    read no `qsave.` slot, then instructions `X` none of which writes an array slot. -/
theorem order_shape (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {A X : Lcmd} (hA : ∀ j ∈ A, srcPlainB j = true)
    (hX : ∀ j ∈ X, noSlotWriteB slotArr j = true) :
    slotAfterSlotReloadFreeB slotArr false (A ++ X) = true ∧ saveSrcB slotArr (A ++ X) = true :=
  ⟨slotAfter_append A (fun j hj => (srcPlain_facts hq (hA j hj)).1) hX,
    saveSrcB_iff.mpr fun j hj => (List.mem_append.mp hj).elim
      (fun hj => (srcPlain_facts hq (hA j hj)).2) (fun hj => saveSrcI_of_noWrite (hX j hj))⟩

/-- **The order conditions of the fused export body.** Under the hypotheses of
    `PhysImgSideAlloc.homeOkB_lfundefPhysAbiOfVirtCert`, the fusion of the export body of
    `lfundefPhysAbiOfVirtCert` writes no array slot behind a reload from an array slot, and
    reloads into an array slot only from names that are no array slots. -/
theorem order_lfundefPhysAbiOfVirtCert {slotArr : String → Option (String × Nat)}
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (mbr : String → Option String)
    (hmbr : mbr = fun base =>
      (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false)
    (hshape : ∀ i ∈ body1, AccForm slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o)
      mbr i.li_i)
    (harr : ∀ i ∈ body1, ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → slotArr q = none)
    (hidx : ∀ i ∈ body1, isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true)
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    let b0 := (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body
    slotAfterSlotReloadFreeB slotArr false (fuseMulHiBody b0 true) = true ∧
      saveSrcB slotArr (fuseMulHiBody b0 true) = true := by
  intro b0
  have hsite := fuseSiteOkB_lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm
    abiArgs abiTyin posBind body1 hb1 mbr hmbr hcf hshape harr hidx hslot
  have hhome := homeOkB_lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm
    abiArgs abiTyin posBind body1 hb1 mbr hmbr hcf hshape harr hidx hslot
  have hord : slotAfterSlotReloadFreeB slotArr false b0 = true ∧ saveSrcB slotArr b0 = true := by
    simp only [b0]
    rw [lfundefPhysAbiOfVirtCert_body virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin
      posBind body1 hb1 mbr hmbr hcf, reloadArrImmBody_filter_flatMap]
    obtain ⟨-, -, -, hD⟩ := physExpand_flatMap_side (certShiftImm shiftImm body1) body1 mbr hcf
      hshape harr hidx hslot
    refine order_shape hslot (fun j hj => ?_) (fun j hj => ?_)
    · rcases List.mem_append.mp hj with hj | hj
      · exact buildPrologue_srcPlain _ _ j hj
      · exact extraSaves_srcPlain _ j hj
    · unfold insertEpilogue at hj
      simp only [List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | (hj | hj) | hj
      · exact noWrite_of_dstOkB (dstOkB_of_dstOk
          (buildArgPtrMaterialize_dstOk hslot _ _ _ _ j hj))
      · exact noWrite_of_dstOkB (hD j (List.dropLast_subset _ hj))
      · exact noWrite_of_dstOkB (dstOkB_of_dstOk (calleeSaveRestoreEpilogue_dstOk hslot j hj))
      · subst hj; rfl
  have hinv := fun (seen : Bool) => fuse_slotAfter true hslot b0 [] [] [] seen hsite hhome
    (EnvAgree.refl _) (fun _ hp => by cases hp) (fun _ hp => by cases hp)
  refine ⟨hinv false hord.1, saveSrcB_iff.mpr fun j hj => ?_⟩
  rcases fuse_mem true hslot b0 [] [] [] hsite hhome (EnvAgree.refl _) (fun _ hp => by cases hp)
    (fun _ hp => by cases hp) j hj with hj | hj
  · exact saveSrcB_iff.mp hord.2 j hj
  · exact saveSrcI_of_noWrite (noWrite_of_dstOkB hj)

/-! ## 4. The runs -/

/-- A run of a body is a sublist of the body. -/
theorem sublist_of_mem_splitStraightRuns {b seg : Lcmd} (h : seg ∈ splitStraightRuns b) :
    seg.Sublist b := by
  have := (List.infix_of_mem_flatten h).sublist
  rwa [splitStraightRuns_flatten] at this

/-- **`elimSideB` on a run.** Let the fusion `Z` of a body satisfy the two order conditions
    and `b1` be a sublist of `Z`. Then every modeled run of `b1` satisfies `elimSideB`. -/
theorem elimSideB_of_run {Z b1 seg : Lcmd}
    (hZ : slotAfterSlotReloadFreeB slotArr false Z = true ∧ saveSrcB slotArr Z = true)
    (hs : b1.Sublist Z) (hseg : seg ∈ splitStraightRuns b1) (hm : bodyAllModeled seg = true) :
    elimSideB slotArr seg = true := by
  have hsub := (sublist_of_mem_splitStraightRuns hseg).trans hs
  simp only [elimSideB, hm, Bool.true_and,
    slotAfterSlotReloadFreeB_sublist hsub (fun h => h) hZ.1, saveSrcB_sublist hsub hZ.2]

/-- **`optSideB` from its three parts.** -/
theorem optSideB_of_loadSide {seg : Lcmd} (h1 : elimSideB slotArr seg = true)
    (h2 : reloadPairSideB slotArr (elimReloads seg) = true)
    (h3 : loadSideB slotArr (LcmdCopyPropagate.copyPropagateBody (LprogScheduler.scheduleBody
      (LcmdReloadElim.reloadElimBody (elimReloads seg)))) = true) :
    optSideB slotArr seg = true := by
  simp [optSideB, h1, h2, h3]

/-! ## 5. The spill pairs -/

section Pairs

open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim (spillStoreKey spillLoadKey
  isRedundantReloadL isSlotName isSlotName_eq_hasPrefix spillStoreKey_eq spillLoadKey_eq
  keys_of_isRedundantReloadL)

/-- The operand names no array slot: a register that is no array slot, or an indexed operand
    whose base and index are none. -/
def GoodOp (slotArr : String → Option (String × Nat)) : LOperand → Prop
  | .reg n => slotArr n = none
  | .arrIdx b y _ => slotArr b = none ∧ slotArr y = none
  | _ => True

@[simp] theorem goodOp_reg {n : String} : GoodOp slotArr (.reg n) ↔ slotArr n = none := Iff.rfl

@[simp] theorem goodOp_arrIdx {b y : String} {s : Nat} :
    GoodOp slotArr (.arrIdx b y s) ↔ slotArr b = none ∧ slotArr y = none := Iff.rfl

@[simp] theorem goodOp_imm {v : Nat} : GoodOp slotArr (.imm v) := trivial

local macro "q_fin" : tactic => `(tactic|
  (simp only [List.forall_mem_cons, List.forall_mem_append] <;> (try and_intros) <;>
    first
      | (intro _ h; exact absurd h List.not_mem_nil)
      | (refine $(Lean.mkIdent `hQ) _ _ _ ?_; simp [*])))

/-- **A property of every instruction of one expansion.** Let `Q` hold of every operation
    whose sources name no array slot, of the memref base reload `ptrLoad q` and of every
    instruction that is no operation. When the operand map sends every operand to one naming
    no array slot and the reload scratches are no array slots, `Q` holds of every instruction
    of `physExpand`. -/
theorem physExpand_forall (Q : LinstrR → Prop)
    (hQ : ∀ ds o ss, (∀ x ∈ ss, GoodOp slotArr x) → Q (.Lopn ds o ss))
    (hR : ∀ q, Q (ptrLoad q))
    (hO : ∀ r, (∀ ds o ss, r ≠ .Lopn ds o ss) → Q r)
    (shiftImm : ShiftImmOracle) (u64 : Bool) (rm : LOperand → LOperand)
    (mbr : String → Option String) (i : Linstr) (hg : ∀ x, GoodOp slotArr (rm x))
    (hs15 : slotArr reloadScratch = none) (hs14 : slotArr reloadScratch2 = none) :
    ∀ r ∈ physExpand shiftImm u64 rm mbr i, Q r.li_i := by
  have hmov : ∀ d s mov, GoodOp slotArr s → ∀ r ∈ legalizeMov d s mov, Q r := by
    intro d s mov hs
    unfold legalizeMov
    split <;> q_fin
  have hbin : ∀ d s opn mov, GoodOp slotArr d → GoodOp slotArr s →
      ∀ r ∈ legalizeBinop d s opn mov, Q r := by
    intro d s opn mov hd hs
    unfold legalizeBinop
    split <;> q_fin
  have hwide : ∀ s mov, GoodOp slotArr s →
      (∀ r ∈ (materializeWideImm s mov).1, Q r) ∧
        GoodOp slotArr (materializeWideImm s mov).2 := by
    intro s mov hs
    unfold materializeWideImm
    split
    · split
      · exact ⟨by q_fin, by simp [hs14]⟩
      · exact ⟨by q_fin, hs⟩
    · exact ⟨by q_fin, hs⟩
  have hsib : ∀ o, GoodOp slotArr o →
      (∀ r ∈ (legalizeSibElem o).1, Q r) ∧ GoodOp slotArr (legalizeSibElem o).2 := by
    intro o ho
    cases o with
    | arrIdx b y sc =>
      simp only [goodOp_arrIdx] at ho
      obtain ⟨hb, hy⟩ := ho
      simp only [legalizeSibElem]
      refine ⟨?_, ?_⟩
      · split_ifs <;> q_fin
      · split_ifs <;> simp [*]
    | _ => exact ⟨by simp [legalizeSibElem], by simp only [legalizeSibElem]; exact ho⟩
  have hrel : ∀ o, GoodOp slotArr o →
      (∀ r ∈ (reloadMemrefBase mbr o).1, Q r) ∧ GoodOp slotArr (reloadMemrefBase mbr o).2 := by
    intro o ho
    cases o with
    | arrIdx b y sc =>
      simp only [goodOp_arrIdx] at ho
      simp only [reloadMemrefBase]
      split
      · refine ⟨?_, by simp [hs14, ho.2]⟩
        intro r hr
        simp only [List.mem_singleton] at hr
        subst hr
        exact hR _
      · exact ⟨by simp, by simpa using ho⟩
    | _ => exact ⟨by simp [reloadMemrefBase], by simp only [reloadMemrefBase]; exact ho⟩
  have hload : ∀ d s opn mov, GoodOp slotArr d → GoodOp slotArr s →
      ∀ r ∈ legalizeMemLoad d s opn mov, Q r := by
    intro d s opn mov hd hs
    obtain ⟨h1, h2⟩ := hsib s hs
    unfold legalizeMemLoad
    rcases he : legalizeSibElem s with ⟨pre, s'⟩
    rw [he] at h1 h2
    simp only at h1 h2 ⊢
    rw [List.forall_mem_append]
    exact ⟨h1, by split <;> q_fin⟩
  have hstore : ∀ k dA addr val opn mov, GoodOp slotArr addr → GoodOp slotArr val →
      ∀ r ∈ legalizeMemStoreK k dA addr val opn mov, Q r := by
    intro k dA addr val opn mov ha hv
    unfold legalizeMemStoreK
    split
    · next l hc =>
      unfold constIdxStore? at hc
      split at hc
      · simp only [goodOp_arrIdx] at ha
        rcases k with _ | c <;> simp at hc
        obtain ⟨-, -, rfl⟩ := hc
        split_ifs <;> q_fin
      · cases hc
    · unfold legalizeMemStore
      obtain ⟨h1, h2⟩ := hsib addr ha
      rcases he : legalizeSibElem addr with ⟨pre, a'⟩
      rw [he] at h1 h2
      simp only at h1 h2 ⊢
      split
      · simp only [goodOp_arrIdx] at h2
        split <;> rw [List.forall_mem_append] <;> exact ⟨h1, by q_fin⟩
      · rw [List.forall_mem_append]; exact ⟨h1, by q_fin⟩
      · rw [List.forall_mem_append]; exact ⟨h1, by q_fin⟩
  have htwo : ∀ d s0 s1 opn mov, GoodOp slotArr d → GoodOp slotArr s0 → GoodOp slotArr s1 →
      ∀ r ∈ lowerTwoAddr d s0 s1 opn mov, Q r := by
    intro d s0 s1 opn mov hd h0 h1
    obtain ⟨w1, w2⟩ := hwide s1 mov h1
    unfold lowerTwoAddr
    rcases he : materializeWideImm s1 mov with ⟨pre, s1'⟩
    rw [he] at w1 w2
    simp only at w1 w2 ⊢
    split
    · simp only [List.forall_mem_append]
      exact ⟨w1, hbin _ _ _ _ hd w2⟩
    · split
      · simp only [List.forall_mem_append]
        refine ⟨⟨w1, ?_⟩, by q_fin⟩
        unfold scratchBinop
        split <;> q_fin
      · simp only [List.forall_mem_append]
        exact ⟨⟨hmov _ _ _ h0, w1⟩, hbin _ _ _ _ hd w2⟩
  have hshift : ∀ d s0 v opn mov, GoodOp slotArr d → GoodOp slotArr s0 →
      ∀ r ∈ lowerTwoAddrShiftImm d s0 v opn mov, Q r := by
    intro d s0 v opn mov hd h0
    unfold lowerTwoAddrShiftImm
    split_ifs
    · q_fin
    · q_fin
    · rw [List.forall_mem_append]
      exact ⟨hmov _ _ _ h0, by q_fin⟩
  have hnat : ∀ d s opn mov, GoodOp slotArr s →
      ∀ r ∈ lowerNativeShiftRotate d s opn mov, Q r := by
    intro d s opn mov hs
    unfold lowerNativeShiftRotate
    split_ifs <;> q_fin
  have hone : ∀ u64 opn d s, GoodOp slotArr s → ∀ r ∈ legalizeOneSrc u64 opn d s, Q r := by
    intro u64 opn d s hs
    unfold legalizeOneSrc
    split
    · exact hmov _ _ _ hs
    · q_fin
  have hspill : ∀ dsts opn srcs, (∀ x ∈ dsts, GoodOp slotArr x) →
      (∀ x ∈ srcs, GoodOp slotArr x) → ∀ r ∈ legalizeSpillDst dsts opn srcs, Q r := by
    intro dsts opn srcs hd hs
    unfold legalizeSpillDst
    split
    · next l h =>
      unfold cmovSpillDst? at h
      split at h
      · split at h
        · cases h
          simp only [List.forall_mem_cons, List.mem_singleton, forall_eq] at hd hs
          unfold cmovSpillSeq
          split_ifs <;> q_fin
        · cases h
      · cases h
    · split
      · next l _ h =>
        unfold setccSpill? at h
        split at h
        · split at h
          · cases h
            simp only [List.forall_mem_cons, List.mem_singleton, forall_eq] at hd hs
            unfold setccMov
            split_ifs <;> q_fin
          · cases h
        · cases h
      · split
        · rename_i h
          unfold andnSpill? andnSpillI? at h
          rw [CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.x86Abi_reload,
            CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.x86Abi_reloadSnd] at h
          split at h
          · split at h
            · cases h
              simp only [List.forall_mem_cons, List.mem_singleton, forall_eq] at hd hs
              q_fin
            · cases h
          · cases h
        · intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact hQ _ _ _ hs
  obtain ⟨ii, w⟩ := i
  have hmap : ∀ (l : List LinstrR), (∀ r ∈ l, Q r) →
      ∀ r ∈ l.map (fun r => (⟨ii, r⟩ : Linstr)), Q r.li_i := by
    intro l hl r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    exact hl r' hr'
  cases w with
  | Lopn ds o ss =>
    rw [physExpand_eq]
    dsimp only
    split
    · rename_i d _ opn s0 s1 _ heq
      cases heq
      have hd := hg d
      have h0 := hg s0
      have h1 := hg s1
      split
      · split
        · exact hmap _ (hshift _ _ _ _ _ hd h0)
        · exact hmap _ (htwo _ _ _ _ _ hd h0 h1)
      · split
        · rename_i d' opn' addr val heq
          cases heq
          split
          · obtain ⟨k1, k2⟩ := hrel _ h0
            intro r hr
            rcases List.mem_append.mp hr with hr | hr
            · exact hmap _ k1 r hr
            · exact hmap _ (hstore _ _ _ _ _ _ k2 h1) r hr
          · exact hmap _ (hspill _ _ _ (by simp [hd]) (by simp [h0, h1]))
        · rename_i heq
          cases heq
          exact hmap _ (hspill _ _ _ (by simp [hg]) (by simp [hg]))
        · rename_i hno
          exact absurd rfl (hno _ _ _)
    · rename_i d opn s heq
      cases heq
      have hd := hg d
      have hs := hg s
      split
      · exact hmap _ (hnat _ _ _ _ hs)
      · split
        · obtain ⟨k1, k2⟩ := hrel _ hs
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact hmap _ k1 r hr
          · exact hmap _ (hload _ _ _ _ hd k2) r hr
        · exact hmap _ (hone _ _ _ _ hs)
    · rename_i dsts opn srcs _ _ heq
      cases heq
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact hQ _ _ _ (by simp [hg])
    · rename_i hno
      exact absurd rfl (hno _ _ _)
  | _ =>
    intro r hr
    simp only [physExpand_eq, List.mem_singleton] at hr
    subst hr
    exact hO _ (by intro ds o ss h; cases h)

/-- No move into a register `r` reads the save slot `qsave.r` of `r` when that slot is an
    array slot. -/
def LoadOkR (slotArr : String → Option (String × Nat)) (i : LinstrR) : Prop :=
  ∀ r mn, i = .Lopn [.reg r] mn [.reg (slotOfReg r)] → slotArr (slotOfReg r) = none

/-- `LoadOkR` of the instruction. -/
def LoadOk (slotArr : String → Option (String × Nat)) (j : Linstr) : Prop := LoadOkR slotArr j.li_i

theorem loadOkR_mov {d s o : String}
    (h : ∀ x, d = x → s = slotOfReg x → slotArr (slotOfReg x) = none) :
    LoadOkR slotArr (.Lopn [.reg d] o [.reg s]) := by
  intro x mn he
  simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at he
  exact h x he.1 he.2.2

theorem ne_slotOfReg {s : String} (h : hasPrefix s "qsave." = false) (x : String) :
    s ≠ slotOfReg x := by
  rintro rfl
  rw [hasPrefix_slotOfReg] at h
  cases h

/-- A spill of a register `r` into an array slot is a save of `r` into its slot `qsave.r`. -/
def StoreSelf (slotArr : String → Option (String × Nat)) (j : Linstr) : Prop :=
  ∀ slot r mn, spillStoreKey j = some (slot, r, mn) → (slotArr slot).isSome = true →
    slot = slotOfReg r

/-- **`reloadPairSideB` from the spill pairs.** When every spill into an array slot is a save
    into the slot of its register and no move reads the array slot of its destination
    register, no deleted reload of a spill pair reads an array slot or a general-purpose
    name. -/
theorem reloadPairSideB_of_pairs :
    ∀ (l : Lcmd), (∀ i ∈ l, StoreSelf slotArr i) → (∀ j ∈ l, LoadOk slotArr j) →
      reloadPairSideB slotArr l = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | i :: j :: rest, hS, hL => by
    simp only [reloadPairSideB, Bool.and_eq_true]
    refine ⟨?_, reloadPairSideB_of_pairs (j :: rest) (fun x hx => hS x
      (List.mem_cons_of_mem _ hx)) (fun x hx => hL x (List.mem_cons_of_mem _ hx))⟩
    cases hred : isRedundantReloadL i j with
    | false => rfl
    | true =>
      obtain ⟨slot, r, mn, hsi, hlj⟩ := keys_of_isRedundantReloadL hred
      simp only [Bool.not_true, Bool.false_or, hlj]
      obtain ⟨hjl, hslot, -, -⟩ := spillLoadKey_eq hlj
      refine Bool.and_eq_true_iff.mpr ⟨?_, by simp [gpNameB_of_isSlotName hslot]⟩
      cases hs : slotArr slot with
      | none => rfl
      | some _ =>
        have he := hS i List.mem_cons_self slot r mn hsi (by simp [hs])
        subst he
        have := hL j (by simp) r mn hjl
        rw [this] at hs
        cases hs

/-- **`reloadPairSideB` on a run.** When the spill pairs of the fusion `Z` satisfy
    `StoreSelf` and `LoadOk` and `b1` is a sublist of `Z`, every run of `b1` satisfies
    `reloadPairSideB` after `elimReloads`. -/
theorem reloadPairSideB_of_run {Z b1 seg : Lcmd} (hS : ∀ i ∈ Z, StoreSelf slotArr i)
    (hL : ∀ j ∈ Z, LoadOk slotArr j) (hs : b1.Sublist Z) (hseg : seg ∈ splitStraightRuns b1) :
    reloadPairSideB slotArr (elimReloads seg) = true := by
  have hsub := ((elimReloads_sublist seg).trans (sublist_of_mem_splitStraightRuns hseg)).trans hs
  exact reloadPairSideB_of_pairs _ (fun i hi => hS i (hsub.subset hi))
    (fun j hj => hL j (hsub.subset hj))

/-- The frame slot an argument is read from is the save slot `qsave.r` of its name `r`. -/
theorem abiSlotOfExt_slotOfReg {r s : String} (h : abiSlotOfExt r = some s) : s = slotOfReg r := by
  unfold abiSlotOfExt at h
  cases h1 : abiSaveOfExt r with
  | some s' =>
    rw [h1] at h
    cases h
    exact (abiSaveOfExt_spec h1).1
  | none =>
    rw [h1] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨-, -, rfl⟩ := h
    rfl

/-- **The spill pairs of the fused export body.** Under the hypotheses of
    `order_lfundefPhysAbiOfVirtCert`, when no operand of a `MULXHI` of the export body is an
    array slot (`hmul`), the save slots of the callee-saved registers are no array slots
    (`hcs`) and no ABI argument name has the prefix `qsave.` (`habi`), every spill of the
    fused body into an array slot is a save into the slot of its register, and no move into
    a register reads the array slot of that register. -/
theorem pairs_lfundefPhysAbiOfVirtCert {slotArr : String → Option (String × Nat)}
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (mbr : String → Option String)
    (hmbr : mbr = fun base =>
      (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false)
    (hshape : ∀ i ∈ body1, AccForm slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o)
      mbr i.li_i)
    (harr : ∀ i ∈ body1, ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → slotArr q = none)
    (hidx : ∀ i ∈ body1, isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true)
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    (hmul : PhysImgSidePass.mulHiNoSlotB slotArr (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs'
      accRegs shiftImm abiArgs abiTyin x86Abi posBind).1.lfd_body = true)
    (hcs : ∀ R ∈ ["RBX", "RBP", "R12", "R13", "R14", "R15"], slotArr (slotOfReg R) = none)
    (habi : ∀ a ∈ abiArgs, hasPrefix a "qsave." = false) :
    let b0 := (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body
    (∀ i ∈ fuseMulHiBody b0 true, StoreSelf slotArr i) ∧
      ∀ j ∈ fuseMulHiBody b0 true, LoadOk slotArr j := by
  intro b0
  have hsite := fuseSiteOkB_lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm
    abiArgs abiTyin posBind body1 hb1 mbr hmbr hcf hshape harr hidx hslot
  have hhome := homeOkB_lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm
    abiArgs abiTyin posBind body1 hb1 mbr hmbr hcf hshape harr hidx hslot
  have h14 : slotArr (slotOfReg reloadScratch2) = none := hcs _ (by simp [reloadScratch2])
  have h15 : slotArr (slotOfReg reloadScratch) = none := hcs _ (by simp [reloadScratch])
  have hs15 : slotArr reloadScratch = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hs14 : slotArr reloadScratch2 = none := slotArr_none_of_prefix hslot (by decide +kernel)
  -- store side: a spill into an array slot writes it
  have hselfW : ∀ i, noSlotWriteB slotArr i = true → StoreSelf slotArr i := by
    intro i hw slot r mn hk hs
    obtain ⟨he, -, -, -⟩ := spillStoreKey_eq hk
    simp [noSlotWriteB, he, writtenNames] at hw
    rw [hw] at hs
    cases hs
  -- the parts of the export body
  have hparts : (∀ i ∈ b0, StoreSelf slotArr i) ∧ ∀ j ∈ b0, LoadOk slotArr j := by
    simp only [b0]
    rw [lfundefPhysAbiOfVirtCert_body virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin
      posBind body1 hb1 mbr hmbr hcf, reloadArrImmBody_filter_flatMap]
    obtain ⟨-, -, -, hD⟩ := physExpand_flatMap_side (certShiftImm shiftImm body1) body1 mbr hcf
      hshape harr hidx hslot
    have hpro := prologue_moves { virt0 with lfd_body := body1 } (physTableOut body1 []) abiArgs
    have hA : ∀ j ∈ buildPrologue { virt0 with lfd_body := body1 } (physTableOut body1 [])
        (fun _ => none) ++ extraSaves abiArgs, StoreSelf slotArr j ∧ LoadOk slotArr j := by
      intro j hj
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hj
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hpro.1 j hj)
      obtain ⟨o, ho⟩ := slotMov?_eq hp
      obtain ⟨d, R⟩ := p
      have h3 := hpro.2.2 k j d R hk hp
      refine ⟨fun slot r mn hkey hsl => ?_, ?_⟩
      · obtain ⟨he, -, -, -⟩ := spillStoreKey_eq hkey
        rw [ho] at he
        simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at he
        obtain ⟨rfl, -, rfl⟩ := he
        by_cases hd : d = reloadScratch2
        · subst hd; rw [hs14] at hsl; cases hsl
        · exact (h3 hd).1
      · show LoadOkR slotArr j.li_i
        rw [ho]
        refine loadOkR_mov fun x hx hR => ?_
        subst hx
        by_cases hd : d = reloadScratch2
        · subst hd; exact h14
        · exact absurd hR (ne_slotOfReg (h3 hd).2.1 _)
    have hM : ∀ j ∈ buildArgPtrMaterialize { virt0 with lfd_body := body1 }
        (physTableOut body1 []) abiArgs (fun _ => none), LoadOk slotArr j := by
      intro j hj
      show LoadOkR slotArr j.li_i
      unfold buildArgPtrMaterialize at hj
      obtain ⟨⟨abiReg, k⟩, hk, hj⟩ := List.mem_flatMap.mp hj
      have hab := habi abiReg (List.fst_mem_of_mem_zipIdx hk)
      simp only at hj
      split at hj
      · simp at hj
      · split_ifs at hj <;>
          rcases hs : abiSlotOfExt abiReg with _ | s <;>
          simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hj
        all_goals rcases hj with rfl | rfl
        all_goals refine loadOkR_mov fun x hx hR => ?_
        all_goals first
          | (subst hx; exact h15)
          | exact absurd hR (ne_slotOfReg (by decide +kernel) _)
          | exact absurd hR (ne_slotOfReg hab _)
          | (exfalso
             have e1 := abiSlotOfExt_slotOfReg hs
             subst e1
             have e2 : abiReg = x := by simpa [slotOfReg] using hR
             exact ‹¬(_ == abiReg) = true› (by rw [hx, e2]; exact beq_self_eq_true _))
    have hrmE : physRmap body1 [] =
        fun o =>
          remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o := by
      simp only [physRmap, hcf, Bool.false_eq_true, ite_false]
    have hP : ∀ p, slotArr (physRegName p x86Abi) = none := fun p =>
      slotArr_none_of_prefix hslot (hasPrefix_qsave_physRegName p)
    have hg : ∀ x, GoodOp slotArr (physRmap body1 [] x) := by
      intro x
      rw [hrmE]
      cases x <;> simp [remapOperand, GoodOp, hP]
    have hF : ∀ j ∈ body1.flatMap (fun i => (reloadArrImmBody mbr
        (physExpand (certShiftImm shiftImm body1) (LprogAsmPrinter.bodyIsU64 body1)
          (physRmap body1 []) mbr i)).filter notLivePin),
        LoadOk slotArr j := by
      intro j hj
      obtain ⟨i, -, hj⟩ := List.mem_flatMap.mp hj
      rcases mem_reloadArrImmBody (List.mem_of_mem_filter hj) with hj | ⟨i', -, l', hl, -, hx⟩
      · refine physExpand_forall (LoadOkR slotArr) (fun ds o ss hss x mn he => ?_)
          (fun q => by
            rcases ptrLoad_cases q with hp | hp <;> rw [hp] <;>
              exact loadOkR_mov fun x hx _ => by subst hx; exact h14)
          (fun r hr x mn he => absurd he (hr _ _ _)) _ _ _ mbr i hg hs15 hs14 j hj
        simp only [LinstrR.Lopn.injEq] at he
        obtain ⟨-, -, rfl⟩ := he
        exact hss _ List.mem_cons_self
      · show LoadOkR slotArr j.li_i
        obtain ⟨b, q, -, ⟨n, w, -, rfl⟩ | ⟨d, v, k, -, rfl⟩⟩ := reloadArrImm_eq_some hl
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx <;> rw [hx]
          all_goals try (rcases ptrLoad_cases q with hp | hp <;> rw [hp])
          all_goals first
            | exact loadOkR_mov fun x hx _ => by subst hx; exact h14
            | (intro x mn he; simp [LinstrR.Lopn.injEq] at he)
        · rcases List.mem_cons.mp hx with hx | hx
          · rw [hx]
            rcases ptrLoad_cases q with hp | hp <;> rw [hp] <;>
              exact loadOkR_mov fun x hx _ => by subst hx; exact h14
          · rcases mem_storeImmVia hx with hx | hx | hx <;> rw [hx]
            · exact loadOkR_mov fun x hx _ => by subst hx; exact h15
            all_goals (intro x mn he; simp [LinstrR.Lopn.injEq] at he)
    have hE : ∀ j ∈ calleeSaveRestoreEpilogue, LoadOk slotArr j := by
      intro j hj
      simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact loadOkR_mov fun x hx _ => by subst hx; exact hcs _ (by simp)
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rcases List.mem_append.mp hj with hj | hj
      · exact (hA j hj).1
      · refine hselfW j ?_
        unfold insertEpilogue at hj
        simp only [List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | (hj | hj) | hj
        · exact noWrite_of_dstOkB (dstOkB_of_dstOk
            (buildArgPtrMaterialize_dstOk hslot _ _ _ _ j hj))
        · exact noWrite_of_dstOkB (hD j (List.dropLast_subset _ hj))
        · exact noWrite_of_dstOkB (dstOkB_of_dstOk (calleeSaveRestoreEpilogue_dstOk hslot j hj))
        · subst hj; rfl
    · rcases List.mem_append.mp hj with hj | hj
      · exact (hA j hj).2
      · unfold insertEpilogue at hj
        simp only [List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | (hj | hj) | hj
        · exact hM j hj
        · exact hF j (List.dropLast_subset _ hj)
        · exact hE j hj
        · subst hj; intro x mn he; cases he
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · rcases fuse_mem true hslot b0 [] [] [] hsite hhome (EnvAgree.refl _)
      (fun _ hp => by cases hp) (fun _ hp => by cases hp) i hi with hi | hi
    · exact hparts.1 i hi
    · exact hselfW i (noWrite_of_dstOkB hi)
  · rcases PhysImgSidePass.mem_fuseMulHiAux true b0 [] [] j hj with hj | ⟨i, hi, d, opn, s1, s2,
      heq, hhi, ds, o, y, hjy, -, hy⟩
    · exact hparts.2 j hj
    · intro x mn he
      rw [hjy] at he
      simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at he
      obtain ⟨-, -, rfl⟩ := he
      have hm := List.all_eq_true.mp hmul i hi
      rw [heq] at hm
      simp only [hhi, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        Option.isNone_iff_eq_none] at hm
      obtain ⟨⟨hd, h1⟩, h2⟩ := hm
      rcases hy with h | h | h | h | h | h
      · rw [h]; exact h1
      · rw [h]; exact h2
      · rw [h]; exact hd
      · exact absurd h (ne_slotOfReg (by decide +kernel) _).symm
      · exact absurd h (ne_slotOfReg (by decide +kernel) _).symm
      · exact absurd h (ne_slotOfReg (by decide +kernel) _).symm

/-- **`optSideB` on every run** of a sublist `b1` of a fusion `Z` with the two order
    conditions and the spill-pair conditions, when every modeled run satisfies `loadSideB`
    on the body the load CSE reads. -/
theorem optSideB_runs {Z b1 : Lcmd}
    (hZ : slotAfterSlotReloadFreeB slotArr false Z = true ∧ saveSrcB slotArr Z = true)
    (hP : (∀ i ∈ Z, StoreSelf slotArr i) ∧ ∀ j ∈ Z, LoadOk slotArr j)
    (hs : b1.Sublist Z)
    (hrest : ∀ seg ∈ splitStraightRuns b1, bodyAllModeled seg = true →
      loadSideB slotArr (LcmdCopyPropagate.copyPropagateBody (LprogScheduler.scheduleBody
        (LcmdReloadElim.reloadElimBody (elimReloads seg)))) = true) :
    (splitStraightRuns b1).all (optSideB slotArr) = true := by
  refine List.all_eq_true.mpr fun seg hseg => ?_
  cases hm : bodyAllModeled seg with
  | false => simp [optSideB, hm]
  | true =>
    exact optSideB_of_loadSide (elimSideB_of_run hZ hs hseg hm)
      (reloadPairSideB_of_run hP.1 hP.2 hs hseg) (hrest seg hseg hm)

end Pairs

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideOpt
