/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit

/-!
# The image class of the region export at the slot map of the gate

The gate of the region route checks the image class `physImgB sl` at the slot map
`sl = slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps))`: the slots of the word-array
parameters of the layout `σ`, with their array names renamed by `renOf ps` and the cell arrays
`R` at length `0`. Whether a slot is an array slot does not depend on `R` and `ps`
(`regionSl_isSome`), and every array slot is a `qsave.` slot (`regionSl_qsave`).

This module discharges at that slot map the hypotheses of
`PhysImgEmit.physImgB_lfundefPhysAbiOfVirtCert` that concern the slot map and the reload
pairs of the export: the allocation `calleeAllocCert none` of the region route, at the export
names `nfAbiNames fname σ` and `posBind := true`. A pair of the export is an array parameter
`argName j` of `σ` with the register `exportReg` of its parameter, and its save slot is the
array slot of that parameter when the export registers of the parameters are distinct
(`nfAbiNames_pairSave`). An access whose base is such a parameter, with a save slot, has a
reloaded base (`baseReloaded_of_pair`).

## Main results

* `regionSl_isSome`, `regionSl_qsave`: the array slots of the slot map of the gate.
* `slotArrOf_slotOfReg`: the slot of the register of a word-array parameter.
* `mem_nfAbiNames_names_iff`: the array names of `nfAbiNames fname σ` are the names
  `argName j` of the word-array parameters of `σ`.
* `nfAbiNames_pairSave`: the save slot of every reload pair of the export is an array slot.
* `baseReloaded_of_pair`: the base of an access at a paired name is reloaded from an array slot.
* `regBaseReloaded_of_pair`: the same for the register base of a `ZEROARR` or `STOREIMM`.
* `accForm_of_accArg`: array accesses at paired parameters have the access form of the image.
* `physImgB_regionExport`: the export body of the region route, before the post passes, is
  in the image class at the slot map of the gate, for an export whose array accesses
  (`LOADIDX`, `STOREIDX`, `ZEROARR`, `STOREIMM`) have the forms `AccArg σ` and whose array
  operands name no `qsave.` slot.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImg

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg physImgB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotArrOf slotRen
  slotArrOf_some)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (slotArrC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open RegionAllocMapAlign RegionAllocMapDom

/-! ## 1. The slot map of the gate -/

/-- **The array slots of the slot map of the gate** are the slots of `sl`, whatever the cell
    arrays `R` and the renaming `ren`. -/
theorem regionSl_isSome (R : Slots) (sl : String → Option (String × Nat))
    (ren : String → String) (q : String) :
    (slotArrC R (slotRen sl ren) q).isSome = (sl q).isSome := by
  simp [slotArrC, slotRen]

/-- **Every array slot of the slot map of the gate is a `qsave.` slot.** -/
theorem regionSl_qsave (R : Slots) (σ : AbiLayout) (nm ren : String → String) :
    ∀ q, (slotArrC R (slotRen (slotArrOf σ nm) ren) q).isSome = true →
      hasPrefix q "qsave." = true := by
  intro q hq
  rw [regionSl_isSome] at hq
  obtain ⟨⟨A, n⟩, h⟩ := Option.isSome_iff_exists.mp hq
  obtain ⟨j, a, -, -, -, rfl⟩ := slotArrOf_some h
  exact hasPrefix_slotOfReg _

/-- **The slot of the register of a word-array parameter.** When the names `nm` of the
    parameter registers of `σ` are distinct, the slot `slotOfReg (nm R)` of the register `R`
    of the word-array parameter `j` of `n` words holds the array `argName j` of length `n`. -/
theorem slotArrOf_slotOfReg {σ : AbiLayout} {nm : String → String}
    (hnd : (σ.args.map fun a => nm a.reg).Nodup) {j : Nat} {a : AbiArg} {n : Nat}
    (hj : σ.args[j]? = some a) (hk : a.kind = .words n) :
    slotArrOf σ nm (slotOfReg (nm a.reg)) = some (argName j, n) := by
  have hlt : j < σ.args.length := (List.getElem?_eq_some_iff.mp hj).1
  have hget : σ.args[j] = a := (List.getElem?_eq_some_iff.mp hj).2
  have hfind : σ.args.findIdx? (fun b => slotOfReg (nm b.reg) == slotOfReg (nm a.reg))
      = some j := by
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hlt, by simp [hget], fun i hi => ?_⟩
    have hil : i < σ.args.length := by omega
    have hne : nm σ.args[i].reg ≠ nm a.reg := by
      intro he
      have h1 : (σ.args.map fun b => nm b.reg)[i]'(by simpa using hil)
          = (σ.args.map fun b => nm b.reg)[j]'(by simpa using hlt) := by
        simp [he, hget]
      have := (List.Nodup.getElem_inj_iff hnd).mp h1
      omega
    simpa [slotOfReg] using hne
  obtain ⟨an, ar, ak⟩ := a
  simp only at hk
  subst hk
  unfold slotArrOf
  simp only [hfind, hj]

/-! ## 2. The reload pairs of the export -/

/-- **The array names of the export names of the direct route** are the names `argName j` of
    the word-array parameters `j` of the layout. -/
theorem mem_nfAbiNames_names_iff (fname : String) (σ : AbiLayout) (j : Nat) :
    argName j ∈ (nfAbiNames fname σ).outArg :: (nfAbiNames fname σ).inArgs ↔
      ∃ a n, σ.args[j]? = some a ∧ a.kind = .words n := by
  constructor
  · intro h
    rcases List.mem_cons.mp h with h | h
    · simp only [nfAbiNames] at h
      cases ho : nfOutIdx σ with
      | none => rw [ho] at h; exact absurd h (argName_ne_empty j)
      | some k =>
        rw [ho] at h
        simp only [Option.map_some, Option.getD_some] at h
        obtain rfl := JasminLsemSimulation.argName_injective h
        unfold nfOutIdx at ho
        split at ho
        · rename_i r m _
          obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp ho
          have hqm := List.mem_of_find?_eq_some hq
          have hqp := List.find?_some hq
          simp only [Bool.and_eq_true, beq_iff_eq] at hqp
          exact ⟨q.1, m, List.mem_zipIdx_iff_getElem?.mp hqm, hqp.2⟩
        · cases ho
    · simp only [nfAbiNames] at h
      obtain ⟨q, hq, hf⟩ := List.mem_filterMap.mp h
      split at hf
      · rename_i m hk
        split at hf
        · cases hf
        · obtain rfl := JasminLsemSimulation.argName_injective (Option.some.inj hf)
          exact ⟨q.1, m, List.mem_zipIdx_iff_getElem?.mp hq, hk⟩
      · cases hf
  · rintro ⟨a, n, hj, hk⟩
    by_cases ho : nfOutIdx σ = some j
    · refine List.mem_cons.mpr (Or.inl ?_)
      simp [nfAbiNames, ho]
    · refine List.mem_cons_of_mem _ ?_
      simp only [nfAbiNames]
      refine List.mem_filterMap.mpr ⟨(a, j), List.mem_zipIdx_iff_getElem?.mpr hj, ?_⟩
      simp only [hk, ho, ite_false]

/-- **The pairs by slot** are the names `argName j` of `names` with the register `abiArgs[j]`. -/
theorem mem_argBasePairsPos_iff {names abiArgs : List String} {p : String × String} :
    p ∈ argBasePairsPos names abiArgs ↔
      ∃ j r, argName j ∈ names ∧ abiArgs[j]? = some r ∧ p = (argName j, r) := by
  constructor
  · intro h
    obtain ⟨nm, hnm, hf⟩ := List.mem_filterMap.mp h
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hf
    have hqp := List.find?_some hq
    simp only [beq_iff_eq] at hqp
    subst hqp
    exact ⟨q.2, q.1, hnm, List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hq), rfl⟩
  · rintro ⟨j, r, hnm, hr, rfl⟩
    refine List.mem_filterMap.mpr ⟨argName j, hnm, ?_⟩
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
      ((List.find?_isSome (p := fun q : String × Nat => argName q.2 == argName j)).mpr
        ⟨(r, j), List.mem_zipIdx_iff_getElem?.mpr hr, by simp⟩)
    have hqp := List.find?_some hq
    simp only [beq_iff_eq] at hqp
    have hqj := JasminLsemSimulation.argName_injective hqp
    have hqm := List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hq)
    rw [hqj, hr] at hqm
    rw [hq]
    obtain ⟨q1, q2⟩ := q
    simp only at hqj hqm
    subst hqj
    simp [Option.some.inj hqm]

/-- **The save slot of every reload pair of the export is an array slot** of the slot map of
    the gate. At the export names `nfAbiNames fname σ` and `posBind := true`, when the export
    registers of the parameters of `σ` are distinct, the save slot `abiSlotOfExt R` of a pair
    `(argName j, R)` is the slot of the word-array parameter `j`. -/
theorem nfAbiNames_pairSave (fname : String) (σ : AbiLayout)
    (hnd : (σ.args.map fun a => exportReg a.reg).Nodup) (R : Slots) (ren : String → String) :
    ∀ p ∈ argBasePairs true (nfAbiNames fname σ).outArg (nfAbiNames fname σ).inArgs
        (nfAbiNames fname σ).abiArgs, ∀ q, abiSlotOfExt p.2 = some q →
      (slotArrC R (slotRen (slotArrOf σ exportReg) ren) q).isSome = true := by
  intro p hp q hq
  obtain ⟨j, r, hnm, hr, rfl⟩ := mem_argBasePairsPos_iff.mp hp
  obtain ⟨a, n, hj, hk⟩ := (mem_nfAbiNames_names_iff fname σ j).mp hnm
  have hra : r = exportReg a.reg := by
    simp only [nfAbiNames, List.getElem?_map, hj, Option.map_some, Option.some.injEq] at hr
    exact hr.symm
  subst hra
  obtain ⟨rfl, -⟩ := abiSlotOfExt_spec hq
  rw [regionSl_isSome, slotArrOf_slotOfReg hnd hj hk]
  rfl

/-- An argument name is no frame slot name. -/
theorem isFrameSlotName_argName (j : Nat) : isFrameSlotName (argName j) = false := by
  have e : ∀ pat : String, pat.toList.head? ≠ some 'a' → pat.toList ≠ [] →
      hasPrefix (argName j) pat = false := by
    intro pat h1 h2
    obtain ⟨c, t, hct⟩ : ∃ c t, pat.toList = c :: t := by
      cases hl : pat.toList with
      | nil => exact absurd hl h2
      | cons c t => exact ⟨c, t, rfl⟩
    have hc : c ≠ 'a' := fun hc => h1 (by rw [hct, hc]; rfl)
    have ha : (argName j).toList = 'a' :: (toString j).toList := by
      simp [argName, String.toList_append]
    simp only [hasPrefix, ha, hct, List.isPrefixOf, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    exact Or.inl hc
  unfold isFrameSlotName
  rw [e "k." (by decide +kernel) (by decide +kernel), e "kv." (by decide +kernel)
    (by decide +kernel), e "qsave." (by decide +kernel) (by decide +kernel),
    e "mem." (by decide +kernel) (by decide +kernel)]
  rfl

/-- **The base of an access at a paired name is reloaded from an array slot.** Let `body1` be
    a call-free allocator input body and `mbr` the memref base reload map of
    `lfundefPhysAbiOfVirtCert` at the pairs `argBasePairs posBind outArg' inArgs' abiArgs`.
    When the save slot of every pair is an array slot, the base `b` of an access that is no
    frame slot name and is the name of a pair with a save slot is reloaded from an array
    slot. -/
theorem baseReloaded_of_pair {slotArr : String → Option (String × Nat)} {body1 : Lcmd}
    {posBind : Bool} {outArg' : String} {inArgs' abiArgs : List String}
    (hcf : bodyHasCall body1 = false)
    (hsave : ∀ p ∈ argBasePairs posBind outArg' inArgs' abiArgs, ∀ q,
      abiSlotOfExt p.2 = some q → (slotArr q).isSome = true)
    {b y : String} (hfr : isFrameSlotName b = false)
    (hb : ∃ p ∈ argBasePairs posBind outArg' inArgs' abiArgs,
      p.1 = b ∧ (abiSlotOfExt p.2).isSome = true) :
    BaseReloaded slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o)
      (fun base =>
        (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
          match abiSlotOfExt p.2 with
          | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
          | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
      b y := by
  obtain ⟨p, hp, rfl, hs⟩ := hb
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hs
  have hst : bodyStraightCall body1 = false := by
    simp [bodyStraightCall, hcf]
  have hkey : physNameForBody body1 (physTableOut body1 []) p.1
      = physRegName (physMapTabled (straightCallComposeTable body1 (physTableOut body1 [] []))
          (nameSlot body1 p.1)) x86Abi := by
    simp [physNameForBody, hfr, hcf, straightCallComposeTable, hst]
  have hmem : (physNameForBody body1 (physTableOut body1 []) p.1, s) ∈
      (argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none) :=
    List.mem_filterMap.mpr ⟨p, hp, by simp [hs]⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp
    ((List.find?_isSome (p := fun e : String × String =>
      e.1 == physNameForBody body1 (physTableOut body1 []) p.1)).mpr ⟨_, hmem, by simp⟩)
  obtain ⟨p', hp', hf⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some he)
  have hq : ∃ q, abiSlotOfExt p'.2 = some q ∧ e.2 = q := by
    revert hf
    cases abiSlotOfExt p'.2 with
    | none => intro hf; cases hf
    | some q => intro hf; cases hf; exact ⟨q, rfl, rfl⟩
  obtain ⟨q, hq, hqe⟩ := hq
  refine ⟨_, _, q, rfl, ?_, hsave p' hp' q hq, abiSlotOfExt_faB hq⟩
  rw [← hkey]
  simp only [he, Option.map_some, hqe]

/-- **The register base of a constant-index array write at a paired name is reloaded from an
    array slot**, under the hypotheses of `baseReloaded_of_pair`. -/
theorem regBaseReloaded_of_pair {slotArr : String → Option (String × Nat)} {body1 : Lcmd}
    {posBind : Bool} {outArg' : String} {inArgs' abiArgs : List String}
    (hcf : bodyHasCall body1 = false)
    (hsave : ∀ p ∈ argBasePairs posBind outArg' inArgs' abiArgs, ∀ q,
      abiSlotOfExt p.2 = some q → (slotArr q).isSome = true)
    {b : String} (hfr : isFrameSlotName b = false)
    (hb : ∃ p ∈ argBasePairs posBind outArg' inArgs' abiArgs,
      p.1 = b ∧ (abiSlotOfExt p.2).isSome = true) :
    RegBaseReloaded slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o)
      (fun base =>
        (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
          match abiSlotOfExt p.2 with
          | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
          | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
      b := by
  obtain ⟨b', y', q, he, hq, hs, hfa⟩ := baseReloaded_of_pair (y := b) hcf hsave hfr hb
  simp only [remapOperand, LOperand.arrIdx.injEq] at he
  exact ⟨b', q, by simp only [remapOperand, he.1], hq, hs, hfa⟩

/-! ## 3. The export body of the region route -/

/-- The parameter `j` of `σ` is a word array whose register has a frame slot
    (`abiSlotOfExt`): one of the six System V argument registers, or a stack word. -/
def ArgSlot (σ : AbiLayout) (j : Nat) : Prop :=
  ∃ a n, σ.args[j]? = some a ∧ a.kind = .words n ∧ (abiSlotOfExt (exportReg a.reg)).isSome = true

/-- **The array accesses of an instruction are at the array parameters of `σ`**: an
    `LOADIDX` is `[.reg d] [.arrIdx (argName j) y 8]`, an `STOREIDX` is
    `[.reg d] [.arrIdx (argName j) y 8, .reg v]`, a `ZEROARR` is `[.reg (argName j)] [#n, #w]`
    and an `STOREIMM` is `[.reg d] [.reg (argName j), .reg v, #k]`, at a parameter `j` with
    `ArgSlot σ j`; and the mnemonic is untagged when its untagged form is one of these four
    (`AccUntagged`). -/
def AccArg (σ : AbiLayout) (i : LinstrR) : Prop :=
  ∀ ds o ss, i = .Lopn ds o ss →
    (o = "LOADIDX" → ∃ d j y, ds = [.reg d] ∧ ss = [.arrIdx (argName j) y 8] ∧ ArgSlot σ j) ∧
    (o = "STOREIDX" → ∃ d j y v, ds = [.reg d] ∧ ss = [.arrIdx (argName j) y 8, .reg v] ∧
      ArgSlot σ j) ∧
    (o = "ZEROARR" → ∃ j n w, ds = [.reg (argName j)] ∧ ss = [.imm n, .imm w] ∧ ArgSlot σ j) ∧
    (o = "STOREIMM" → ∃ d j v k, ds = [.reg d] ∧ ss = [.reg (argName j), .reg v, .imm k] ∧
      ArgSlot σ j) ∧
    AccUntagged o

/-- **The call-free looped physical ABI export emits no `ZEROARR` or `STOREIMM`**, under the
    hypotheses of `physImgB_lfundefPhysAbiOfVirtCert`, when `body1` has no `ZEROARR` and no
    `STOREIMM` (`hne`): the prologue and the argument pointers are moves, the epilogue is
    moves and a return, every instruction emitted for an instruction of `body1` is under its
    mnemonic or a move mnemonic, and the constant-shape base reload rewrites none of them. -/
theorem arrImmFree_lfundefPhysAbiOfVirtCert {slotArr : String → Option (String × Nat)}
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
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    (hne : ∀ i ∈ body1, ∀ ds o ss, i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM") :
    ∀ j ∈ (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body, isArrImmB j.li_i = false := by
  have hb : ∃ sh cab, (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body =
      (buildPrologue { virt0 with lfd_body := body1 } (physTableOut body1 []) (fun _ => none)
          ++ extraSaves abiArgs) ++
        buildArgPtrMaterialize { virt0 with lfd_body := body1 } (physTableOut body1 []) abiArgs
            (fun _ => none) ++
          insertEpilogue (reloadArrImmBody mbr ((physBodyWithStores sh body1 (fun _ => none)
            reloadScratch2 [] reloadScratch2 0 mbr cab).filter
              fun r => match r.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true))
            calleeSaveRestoreEpilogue := by
    subst hb1 hmbr
    simp only [lfundefPhysAbiOfVirtCert]
    exact ⟨_, _, rfl⟩
  obtain ⟨sh, cab, hb⟩ := hb
  rw [hb]
  have hs15 : slotArr reloadScratch = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hs14 : slotArr reloadScratch2 = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hmem : ∀ c, slotArr ("mem." ++ c) = none := fun c =>
    slotArr_none_of_prefix hslot (hasPrefix_qsave_mem c)
  have hP : ∀ p, slotArr (physRegName p x86Abi) = none := fun p =>
    slotArr_none_of_prefix hslot (hasPrefix_qsave_physRegName p)
  have hcall : ∀ i ∈ body1, ∀ a b, i.li_i ≠ .Lcall a b := by
    intro i hi a b he
    have := List.any_eq_false.mp hcf i hi
    rw [he] at this
    exact this rfl
  have hok : ∀ i ∈ body1, ∀ x ∈ lopnOperands i.li_i, OperandOk slotArr
      ((fun o => remapOperand body1
        (straightCallComposeTable body1 (physTableOut body1 [] [])) o) x) := by
    intro i hi x hx
    cases x with
    | reg n => exact ⟨fun q hq => by cases hq; exact hP _, nofun, nofun⟩
    | arrIdx b y s => exact ⟨nofun, nofun, fun q j sc hq => by cases hq; exact hP _⟩
    | arr q n => exact ⟨nofun, fun q' n' hq => by cases hq; exact harr i hi q n hx, nofun⟩
    | imm _ => exact ⟨nofun, nofun, nofun⟩
  have hold : ∀ j ∈ (physBodyWithStores sh body1 (fun _ => none) reloadScratch2 []
      reloadScratch2 0 mbr cab).filter
        (fun r => match r.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true),
      isArrImmB j.li_i = false := by
    intro j hj
    have hj' := List.mem_of_mem_filter hj
    rw [physBodyWithStores_eq_flatMap] at hj'
    obtain ⟨⟨i, k⟩, hp, hj'⟩ := List.mem_flatMap.mp hj'
    have hi := List.fst_mem_of_mem_zipIdx hp
    have hblk := physPositionEmit_blockOk sh body1 reloadScratch2 reloadScratch2 0 mbr cab []
      i k _ (by simp [hcf]) (hcall i hi) hs15 hs14 hmem (hok i hi) (fun n => ⟨_, rfl⟩)
      (hshape i hi) (hne i hi)
    cases hx : j.li_i with
    | Lopn ds o ss =>
      rcases (hblk.1 j hj' ds o ss hx).2 with ho | ho
      · cases hii : i.li_i with
        | Lopn ds' o' ss' =>
          rw [hii] at ho
          simp only [opnOf, Option.some.injEq] at ho
          subst ho
          obtain ⟨h1, h2⟩ := hne i hi ds' o ss' hii
          have hU := ((hshape i hi) ds' o ss' hii).2.2.2.2
          simp [isArrImmB, untagCaret_ne_of_accUntagged hU (by simp) h1,
            untagCaret_ne_of_accUntagged hU (by simp) h2]
        | _ => rw [hii] at ho; simp [opnOf] at ho
      · exact isArrImmB_of_movMnems ho
    | _ => rfl
  obtain ⟨hpre, -, -⟩ := prologue_moves { virt0 with lfd_body := body1 } (physTableOut body1 [])
    abiArgs
  intro j hj
  simp only [insertEpilogue, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with (hj | hj) | ((hj | hj) | rfl)
  · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hpre j (List.mem_append.mpr hj))
    exact isArrImmB_of_slotMov hq
  · exact buildArgPtrMaterialize_noArrImm _ _ _ _ j hj
  · rcases mem_reloadArrImmBody (List.dropLast_subset _ hj) with hj | ⟨i', hi', l', hl, -, -⟩
    · exact hold j hj
    · have h' := hold i' hi'
      obtain ⟨b, q, -, ⟨n, w, he, -⟩ | ⟨d, v, k, he, -⟩⟩ := reloadArrImm_eq_some hl <;>
        rw [he] at h' <;> simp [isArrImmB] at h'
  · simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rfl

/-- Every parameter `j` with `ArgSlot σ j` is the name of a pair of the export names
    `nfAbiNames fname σ` with a save slot. -/
theorem argPair_nfAbiNames (fname : String) (σ : AbiLayout) (j : Nat) (hj : ArgSlot σ j) :
    ∃ q ∈ argBasePairs true (nfAbiNames fname σ).outArg (nfAbiNames fname σ).inArgs
      (nfAbiNames fname σ).abiArgs, q.1 = argName j ∧ (abiSlotOfExt q.2).isSome = true := by
  obtain ⟨a', n, hj, hk, hsv⟩ := hj
  refine ⟨(argName j, exportReg a'.reg), mem_argBasePairsPos_iff.mpr
    ⟨j, _, (mem_nfAbiNames_names_iff fname σ j).mpr ⟨a', n, hj, hk⟩, ?_, rfl⟩, rfl, hsv⟩
  simp [nfAbiNames, hj]

/-- **Array accesses at paired parameters have the access form of the image**: an
    instruction of a call-free body whose array accesses are at parameters `j` with
    `ArgSlot σ j` (`AccArg σ`), each the name of a pair with an array save slot, has the form
    `AccForm` with every base reloaded. -/
theorem accForm_of_accArg {σ : AbiLayout} {slotArr : String → Option (String × Nat)}
    {body1 : Lcmd} {outArg' : String} {inArgs' abiArgs : List String}
    (hcf : bodyHasCall body1 = false)
    (hsave : ∀ p ∈ argBasePairs true outArg' inArgs' abiArgs, ∀ q,
      abiSlotOfExt p.2 = some q → (slotArr q).isSome = true)
    (hpair : ∀ j, ArgSlot σ j → ∃ q ∈ argBasePairs true outArg' inArgs' abiArgs,
      q.1 = argName j ∧ (abiSlotOfExt q.2).isSome = true)
    {w : LinstrR} (h : AccArg σ w) :
    AccForm slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o)
      (fun base =>
        (((argBasePairs true outArg' inArgs' abiArgs).filterMap (fun p =>
          match abiSlotOfExt p.2 with
          | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
          | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
      w := by
  intro ds o ss he
  obtain ⟨hL, hS, hZ, hI, hU⟩ := h ds o ss he
  refine ⟨fun ho => ?_, fun ho => ?_, fun ho => ?_, fun ho => ?_, hU⟩
  · obtain ⟨d, j, y, rfl, rfl, hj⟩ := hL ho
    exact ⟨d, argName j, y, rfl, rfl,
      baseReloaded_of_pair hcf hsave (isFrameSlotName_argName j) (hpair j hj)⟩
  · obtain ⟨d, j, y, v, rfl, rfl, hj⟩ := hS ho
    exact ⟨d, argName j, y, v, rfl, rfl,
      baseReloaded_of_pair hcf hsave (isFrameSlotName_argName j) (hpair j hj)⟩
  · obtain ⟨j, n, w, rfl, rfl, hj⟩ := hZ ho
    exact ⟨argName j, n, w, rfl, rfl,
      regBaseReloaded_of_pair hcf hsave (isFrameSlotName_argName j) (hpair j hj)⟩
  · obtain ⟨d, j, v, k, rfl, rfl, hj⟩ := hI ho
    exact ⟨d, argName j, v, k, rfl, rfl,
      regBaseReloaded_of_pair hcf hsave (isFrameSlotName_argName j) (hpair j hj)⟩

/-- **The export body of the region route is in the image class at the slot map of the
    gate.** Let `p` pass `regionExportableB`, have no `call` and the export `r`, at a result
    other than one register, and let `a` be the export names `nfAbiNames fname σ`, with
    distinct export registers of the parameters of `σ`. The allocation `calleeAllocCert none`
    that `regionLprogC a p` makes, on the body `arrBasePins a ac` followed by the code `ac`
    given to the allocation and a return, has its function body, before the post passes, in
    the class `physImgB` at the slot map `slotArrC R (slotRen (slotArrOf σ exportReg)
    (renOf ps))` of the gate, for all cell arrays `R` and pairs `ps`, when every instruction
    of the allocator input body `regionAllocBody a Γ.length ts r` has its array accesses at
    array parameters of `σ` with a save slot (`AccArg σ`) and names no `qsave.` slot in an
    array operand. -/
theorem physImgB_regionExport (fname : String) (σ : AbiLayout)
    {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length fname p Γ.length 0 x86Data = some r)
    (hts : ∀ w, ts ≠ [.reg w]) (fd0 : Lfundef)
    (hnd : (σ.args.map fun a => exportReg a.reg).Nodup)
    (hacc : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r, AccArg σ i.li_i)
    (harr : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r, ∀ q n,
      LOperand.arr q n ∈ lopnOperands i.li_i → hasPrefix q "qsave." = false)
    (R : Slots) (ps : List (String × String)) :
    physImgB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
      (calleeAllocCert none
        { fd0 with lfd_body :=
            (arrBasePins (nfAbiNames fname σ)
                (regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code
                  r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res))
              ++ ((regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code
                  r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res)).map (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩])) }
        (nfAbiNames fname σ).outArg (nfAbiNames fname σ).inArgs
        (nfAbiNames fname σ).abiArgs noSplit).1.lfd_body = true := by
  have hB : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r, ShapeB i.li_i :=
    shapeB_regionAllocBody _ _ ts r fun i hi =>
      (exportR_mnemDom Γ.length fname p hp hc _ _ r hr i hi).2.2
  have hcf := bodyHasCall_of_shapeB hB
  have hslot := regionSl_qsave R σ exportReg (renOf ps)
  have hsave := nfAbiNames_pairSave fname σ hnd R (renOf ps)
  have hb1 : regionAllocBody (nfAbiNames fname σ) Γ.length ts r =
      (if (nfAbiNames fname σ).abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range (nfAbiNames fname σ).abiArgs.length).map
            (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (([] : List String).foldl (fun b r => aliasRegBody r (nfAbiNames fname σ).outArg b)
            (arrBasePins (nfAbiNames fname σ)
                (regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code
                  r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res))
              ++ ((regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts
                  r.code r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res)).map (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]))) := by
    unfold regionAllocBody
    split
    · exact absurd rfl (hts _)
    · rfl
  have hshape : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r,
      AccForm (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
        (fun o => remapOperand (regionAllocBody (nfAbiNames fname σ) Γ.length ts r)
          (straightCallComposeTable (regionAllocBody (nfAbiNames fname σ) Γ.length ts r)
            (physTableOut (regionAllocBody (nfAbiNames fname σ) Γ.length ts r) [] [])) o)
        (fun base =>
          (((argBasePairs true (nfAbiNames fname σ).outArg (nfAbiNames fname σ).inArgs
            (nfAbiNames fname σ).abiArgs).filterMap (fun p =>
            match abiSlotOfExt p.2 with
            | some saveName => some (physNameForBody
                (regionAllocBody (nfAbiNames fname σ) Γ.length ts r)
                (physTableOut (regionAllocBody (nfAbiNames fname σ) Γ.length ts r) []) p.1,
                saveName)
            | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
        i.li_i := fun i hi =>
    accForm_of_accArg hcf hsave (argPair_nfAbiNames fname σ) (hacc i hi)
  have harr' : ∀ i ∈ regionAllocBody (nfAbiNames fname σ) Γ.length ts r, ∀ q n,
      LOperand.arr q n ∈ lopnOperands i.li_i →
        slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)) q = none :=
    fun i hi q n hx => slotArr_none_of_prefix hslot (harr i hi q n hx)
  unfold calleeAllocCert
  exact physImgB_lfundefPhysAbiOfVirtCert _ _ _ [] (fun _ => none) _ _ true _ hb1 _ rfl hcf
    hshape harr' hslot

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImg
