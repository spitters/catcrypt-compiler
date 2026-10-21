/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFuse

/-!
# The fusion side conditions on the looped physical ABI export

The looped physical ABI export `lfundefPhysAbiOfVirtCert` of a call-free body is the
prologue, the saves of the further argument registers, the argument materialization, the
flat map of the per-instruction expansion `physExpand` without its `LIVEPIN` instructions,
the callee-saved restores and the return (`lfundefPhysAbiOfVirtCert_body`). This module
proves on that body the two side conditions of the high-product fusion
(`PhysImgFuse.fuseSiteOkB`, `PhysImgFuse.homeOkB`).

The site condition asks, behind every rewritten `MULXHI`, that no array slot is written and
that the reload scan of every base of an indexed operand at stride `8` ends inside the rest of
the body (`ScanStays`). The scan is local (`scanExit_append_left`, `scanExit_append_right`),
so `ScanStays` is closed under concatenation, and the property that every suffix behind a
site has it (`SiteStays`) is closed under concatenation with a right part that has it. An
expansion of an indexed access is a reload window: the reload `MOVQ R14, q` of an array slot,
moves into `R15`, and one instruction through `R14` (`scanStays_window`). Every other
expansion carries no indexed operand when its virtual instruction carries none
(`physExpand_idxFree`).

The home condition asks of every low `MUL` that its destination, and the name the scratch
environment resolves it to, are no array slots. A low `MUL` arises only from the two-address
lowering of a virtual `MUL`; its destination is the allocated register of the virtual
destination or `R15`, and `R15` holds there the destination moved into it by the same
lowering (`homeOkB_lowerTwoAddr`).

## Main results

* `lfundefPhysAbiOfVirtCert_body`: the body of the call-free looped physical ABI export.
* `scanStays_window`, `loadIdx_scanStays`, `storeIdx_scanStays`: the reload windows of the
  access arms keep their scans.
* `physExpand_idxFree`: an expansion of an instruction without indexed operand has none.
* `homeOkB_lowerTwoAddr`, `physExpand_homeOkB`: the home condition on one expansion.
* `fuseSiteOkB_lfundefPhysAbiOfVirtCert`, `homeOkB_lfundefPhysAbiOfVirtCert`: the two side
  conditions of the fusion on the export.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFuse
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
  (physExpand physRmap notLivePin physBodyWithStores_eq_physExpand
    physPositionEmit_eq_physExpand)

/-! ## 1. The body of the export -/

/-- The shift-count oracle of `lfundefPhysAbiOfVirtCert` on the allocator input `body1`: the
    caller's, then the constant-move table of `body1`. -/
def certShiftImm (shiftImm : ShiftImmOracle) (body1 : Lcmd) : ShiftImmOracle := fun nm =>
  match shiftImm nm with
  | some v => some v
  | none => movImmLookup (movImmTable body1) nm

/-- **The body of the call-free looped physical ABI export.** For the allocator input
    `body1` of `lfundefPhysAbiOfVirtCert` and its memref base reload map `mbr`, a body
    without calls exports to the prologue, the saves of the further argument registers, the
    argument materialization, the flat map of `physExpand` over `body1` without its
    `LIVEPIN` instructions, the callee-saved restores and the return. -/
theorem lfundefPhysAbiOfVirtCert_body
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
        match abiSaveOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false) :
    (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body =
      (buildPrologue { virt0 with lfd_body := body1 } (physTableOut body1 []) (fun _ => none)
          ++ extraSaves abiArgs) ++
        (buildArgPtrMaterialize { virt0 with lfd_body := body1 } (physTableOut body1 [])
            abiArgs (fun _ => none) ++
          insertEpilogue ((body1.flatMap (physExpand (certShiftImm shiftImm body1)
              (LprogAsmPrinter.bodyIsU64 body1) (physRmap body1 []) mbr)).filter notLivePin)
            calleeSaveRestoreEpilogue) := by
  have hcall : ∀ i ∈ body1, ∀ a b, i.li_i ≠ .Lcall a b := by
    intro i hi a b he
    have := List.any_eq_false.mp hcf i hi
    rw [he] at this
    exact this rfl
  have hb : ∃ cab, (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body =
      (buildPrologue { virt0 with lfd_body := body1 } (physTableOut body1 []) (fun _ => none)
          ++ extraSaves abiArgs) ++
        buildArgPtrMaterialize { virt0 with lfd_body := body1 } (physTableOut body1 []) abiArgs
            (fun _ => none) ++
          insertEpilogue ((physBodyWithStores (certShiftImm shiftImm body1) body1
            (fun _ => none) reloadScratch2 [] reloadScratch2 0 mbr cab).filter notLivePin)
            calleeSaveRestoreEpilogue := by
    subst hb1 hmbr
    simp only [lfundefPhysAbiOfVirtCert]
    exact ⟨_, rfl⟩
  obtain ⟨cab, hb⟩ := hb
  rw [hb, List.append_assoc, physBodyWithStores_eq_physExpand _ _ _ _ _ _ _ [] hcall]

/-! ## 2. The reload scan is local -/

theorem scanExit_append_left (slotArr : String → Option (String × Nat)) (a c : Lcmd) :
    ∀ (k : Nat) (x : String), k ≤ a.length →
      scanExit slotArr (a ++ c) k x = scanExit slotArr a k x
  | 0, _, _ => rfl
  | k + 1, x, hk => by
    have ih := scanExit_append_left slotArr a c k
    have hg : (a ++ c)[k]? = a[k]? := List.getElem?_append_left (by omega)
    simp only [scanExit, hg]
    cases a[k]? with
    | none => rfl
    | some j =>
      simp only
      cases slotMov? j.li_i with
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only
        split_ifs <;> first | exact ih _ (by omega) | rfl
      | none =>
        simp only
        cases j.li_i with
        | Lopn ds o ss =>
          simp only
          split_ifs
          · rfl
          · exact ih _ (by omega)
        | _ => rfl

/-- The scan of `a ++ c` from position `k` of `c` is the scan of `c`, continued into `a` with
    the name it carries out of `c`. -/
theorem scanExit_append_right (slotArr : String → Option (String × Nat)) (a c : Lcmd) :
    ∀ (k : Nat) (x : String), scanExit slotArr (a ++ c) (a.length + k) x =
      (scanExit slotArr c k x).bind (scanExit slotArr a a.length)
  | 0, x => by
    simpa [scanExit] using scanExit_append_left slotArr a c a.length x le_rfl
  | k + 1, x => by
    have ih := scanExit_append_right slotArr a c k
    have hg : (a ++ c)[a.length + k]? = c[k]? := by
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    rw [show a.length + (k + 1) = (a.length + k) + 1 from rfl]
    simp only [scanExit, hg]
    cases c[k]? with
    | none => rfl
    | some j =>
      simp only
      cases slotMov? j.li_i with
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only
        split_ifs <;> first | exact ih _ | rfl
      | none =>
        simp only
        cases j.li_i with
        | Lopn ds o ss =>
          simp only
          split_ifs
          · rfl
          · exact ih _
        | _ => rfl

/-- The reload scan of every base of an indexed operand at stride `8` in first source position
    ends inside `c`: the statement of `scanStaysB`. -/
def ScanStays (slotArr : String → Option (String × Nat)) (c : Lcmd) : Prop :=
  ∀ k i, c[k]? = some i → ∀ ds o x y ss, i.li_i = .Lopn ds o (.arrIdx x y 8 :: ss) →
    scanExit slotArr c k x = none

variable {slotArr : String → Option (String × Nat)}

theorem scanStaysB_of_scanStays {c : Lcmd} (h : ScanStays slotArr c) :
    scanStaysB slotArr c = true := by
  unfold scanStaysB
  refine List.all_eq_true.mpr fun k hk => ?_
  have hget := List.getElem?_eq_getElem (List.mem_range.mp hk)
  rw [hget]
  simp only
  split
  · rename_i ds o x y sc ss hx
    by_cases h8 : sc = 8
    · subst h8
      simp [h k _ hget ds o x y ss hx]
    · simp [h8]
  · rfl

theorem ScanStays.append {a c : Lcmd} (ha : ScanStays slotArr a) (hc : ScanStays slotArr c) :
    ScanStays slotArr (a ++ c) := by
  intro k i hk ds o x y ss hx
  by_cases hlt : k < a.length
  · rw [List.getElem?_append_left hlt] at hk
    rw [scanExit_append_left slotArr a c k x (by omega)]
    exact ha k i hk ds o x y ss hx
  · rw [List.getElem?_append_right (by omega)] at hk
    obtain ⟨m, rfl⟩ : ∃ m, k = a.length + m := ⟨k - a.length, by omega⟩
    rw [Nat.add_sub_cancel_left] at hk
    rw [scanExit_append_right, hc m i hk ds o x y ss hx]
    rfl

theorem ScanStays.nil : ScanStays slotArr [] := by
  intro k i hk; simp at hk

theorem ScanStays.flatMap {α : Type} {l : List α} {f : α → Lcmd}
    (h : ∀ a ∈ l, ScanStays slotArr (f a)) : ScanStays slotArr (l.flatMap f) := by
  induction l with
  | nil => exact ScanStays.nil
  | cons a l ih =>
    rw [List.flatMap_cons]
    exact (h a List.mem_cons_self).append (ih fun a' ha' => h a' (List.mem_cons_of_mem a ha'))

theorem ScanStays.take {l : Lcmd} (h : ScanStays slotArr l) (n : Nat) :
    ScanStays slotArr (l.take n) := by
  intro k i hk ds o x y ss hx
  have hlt : k < (l.take n).length := (List.getElem?_eq_some_iff.mp hk).1
  have hl : l = l.take n ++ l.drop n := (List.take_append_drop n l).symm
  have hk' : l[k]? = some i := by
    rw [hl, List.getElem?_append_left hlt]; exact hk
  rw [← scanExit_append_left slotArr (l.take n) (l.drop n) k x (by omega), ← hl]
  exact h k i hk' ds o x y ss hx

theorem ScanStays.dropLast {l : Lcmd} (h : ScanStays slotArr l) :
    ScanStays slotArr l.dropLast := by
  rw [List.dropLast_eq_take]; exact h.take _

/-- Every suffix behind a rewritable `MULXHI` keeps its scans. -/
def SiteStays (slotArr : String → Option (String × Nat)) (c : Lcmd) : Prop :=
  ∀ n i, c[n]? = some i → mulHiSiteB i = true → ScanStays slotArr (c.drop (n + 1))

theorem SiteStays.of_noSite {c : Lcmd} (h : ∀ i ∈ c, mulHiSiteB i = false) :
    SiteStays slotArr c := by
  intro n i hn hs
  rw [h i (List.mem_of_getElem? hn)] at hs
  cases hs

theorem SiteStays.append {a c : Lcmd} (ha : SiteStays slotArr a) (hc : SiteStays slotArr c)
    (hcs : ScanStays slotArr c) : SiteStays slotArr (a ++ c) := by
  intro n i hn hs
  by_cases hlt : n < a.length
  · rw [List.getElem?_append_left hlt] at hn
    rw [List.drop_append_of_le_length (by omega)]
    exact (ha n i hn hs).append hcs
  · rw [List.getElem?_append_right (by omega)] at hn
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show n + 1 - a.length = (n - a.length) + 1 by omega]
    exact hc _ i hn hs

theorem SiteStays.nil : SiteStays slotArr [] := by
  intro n i hn; simp at hn

theorem SiteStays.flatMap {α : Type} {l : List α} {f : α → Lcmd}
    (h : ∀ a ∈ l, SiteStays slotArr (f a) ∧ ScanStays slotArr (f a)) :
    SiteStays slotArr (l.flatMap f) ∧ ScanStays slotArr (l.flatMap f) := by
  induction l with
  | nil => exact ⟨SiteStays.nil, ScanStays.nil⟩
  | cons a l ih =>
    rw [List.flatMap_cons]
    obtain ⟨h1, h2⟩ := h a List.mem_cons_self
    obtain ⟨i1, i2⟩ := ih fun a' ha' => h a' (List.mem_cons_of_mem a ha')
    exact ⟨h1.append i1 i2, h2.append i2⟩

theorem SiteStays.dropLast {l : Lcmd} (h : SiteStays slotArr l) :
    SiteStays slotArr l.dropLast := by
  intro n i hn hs
  have hlt : n < l.dropLast.length := (List.getElem?_eq_some_iff.mp hn).1
  have hn' : l[n]? = some i := by
    rw [List.getElem?_dropLast] at hn
    split at hn
    · exact hn
    · cases hn
  rw [List.dropLast_eq_take, List.drop_take]
  exact (h n i hn' hs).take _

/-! ## 3. The site condition from its statements -/

theorem operandOkB_of_operandOk {x : LOperand} (h : OperandOk slotArr x) :
    operandOkB slotArr x = true := by
  obtain ⟨h1, h2, h3⟩ := h
  cases x with
  | reg q => simp [operandOkB, h1 q rfl]
  | arr q n => simp [operandOkB, h2 q n rfl]
  | arrIdx q j sc => simp [operandOkB, h3 q j sc rfl]
  | imm _ => rfl

theorem dstOkB_of_dstOk {r : LinstrR} (h : DstOk slotArr r) : dstOkB slotArr r = true := by
  cases r with
  | Lopn ds o ss =>
    exact List.all_eq_true.mpr fun x hx => operandOkB_of_operandOk (h ds o ss rfl x hx)
  | _ => rfl

/-- **The site condition from its statements.** A body every suffix of which behind a site
    keeps its scans, and every instruction of which from a site on writes no array slot,
    satisfies `fuseSiteOkB`. -/
theorem fuseSiteOkB_of : ∀ {c : Lcmd}, SiteStays slotArr c →
    (∀ n i, c[n]? = some i → mulHiSiteB i = true → ∀ r ∈ c.drop n, dstOkB slotArr r.li_i) →
    fuseSiteOkB slotArr c = true
  | [], _, _ => rfl
  | i :: rest, hs, hd => by
    simp only [fuseSiteOkB, Bool.and_eq_true]
    refine ⟨?_, fuseSiteOkB_of (fun n j hn hj => hs (n + 1) j hn hj)
      (fun n j hn hj => hd (n + 1) j hn hj)⟩
    cases hsi : mulHiSiteB i
    · rfl
    · have h0 := hd 0 i rfl hsi
      simp only [List.drop_zero, List.mem_cons, forall_eq_or_imp] at h0
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true]
      exact ⟨⟨h0.1, List.all_eq_true.mpr h0.2⟩, scanStaysB_of_scanStays (hs 0 i rfl hsi)⟩

/-! ## 4. Instructions without indexed operand -/

/-- The operand is not register-indexed. -/
def noIdxB : LOperand → Bool
  | .arrIdx _ _ _ => false
  | _ => true

/-- No source of the instruction is register-indexed. -/
def idxFreeB : LinstrR → Bool
  | .Lopn _ _ ss => ss.all noIdxB
  | _ => true

@[simp] theorem noIdxB_reg (n : String) : noIdxB (.reg n) = true := rfl

@[simp] theorem noIdxB_imm (v : Nat) : noIdxB (.imm v) = true := rfl

@[simp] theorem noIdxB_arrIdx (b i : String) (sc : Nat) : noIdxB (.arrIdx b i sc) = false :=
  rfl

theorem scanStays_of_idxFree {c : Lcmd} (h : ∀ r ∈ c, idxFreeB r.li_i = true) :
    ScanStays slotArr c := by
  intro k i hk ds o x y ss hx
  have := h i (List.mem_of_getElem? hk)
  rw [hx] at this
  simp [idxFreeB] at this

theorem siteStays_of_idxFree {c : Lcmd} (h : ∀ r ∈ c, idxFreeB r.li_i = true) :
    SiteStays slotArr c :=
  fun _ _ _ _ => scanStays_of_idxFree fun r hr => h r (List.mem_of_mem_drop hr)

theorem legalizeMov_idxFree (d s : LOperand) (mov : String) (hs : noIdxB s = true) : ∀ r ∈ legalizeMov d s mov, idxFreeB r = true := by
  unfold legalizeMov
  split <;> simp [idxFreeB, hs]

theorem legalizeBinop_idxFree (d s : LOperand) (opn mov : String) (hd : noIdxB d = true)
    (hs : noIdxB s = true) : ∀ r ∈ legalizeBinop d s opn mov, idxFreeB r = true := by
  unfold legalizeBinop
  split <;> simp [idxFreeB, hs, hd]

theorem materializeWideImm_idxFree (s : LOperand) (mov : String) (hs : noIdxB s = true) :
    (∀ r ∈ (materializeWideImm s mov).1, idxFreeB r = true) ∧
      noIdxB (materializeWideImm s mov).2 = true := by
  unfold materializeWideImm
  split
  · split <;> simp [idxFreeB, hs]
  · simp [hs]

theorem lowerTwoAddr_idxFree (d s0 s1 : LOperand) (opn mov : String) (hd : noIdxB d = true)
    (h0 : noIdxB s0 = true) (h1 : noIdxB s1 = true) :
    ∀ r ∈ lowerTwoAddr d s0 s1 opn mov, idxFreeB r = true := by
  have hw := materializeWideImm_idxFree s1 mov h1
  unfold lowerTwoAddr
  rcases hmw : materializeWideImm s1 mov with ⟨pre, s1v⟩
  rw [hmw] at hw
  simp only at hw ⊢
  intro r hr
  split at hr <;> simp only [List.mem_append] at hr
  · exact hr.elim (hw.1 r) (legalizeBinop_idxFree d s1v opn mov hd hw.2 r)
  · exact hr.elim (fun h => h.elim (legalizeMov_idxFree d s0 mov h0 r) (hw.1 r))
      (legalizeBinop_idxFree d s1v opn mov hd hw.2 r)

theorem lowerTwoAddrShiftImm_idxFree (d s0 : LOperand) (v : Nat) (opn mov : String)
    (hd : noIdxB d = true) (h0 : noIdxB s0 = true) :
    ∀ r ∈ lowerTwoAddrShiftImm d s0 v opn mov, idxFreeB r = true := by
  unfold lowerTwoAddrShiftImm
  intro r hr
  split at hr
  · simp at hr; rcases hr with rfl | rfl | rfl <;> simp [idxFreeB, h0]
  · split at hr
    · simp at hr; subst hr; simp [idxFreeB, hd]
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact legalizeMov_idxFree d s0 mov h0 r hr
      · simp [idxFreeB, hd]

theorem lowerNativeShiftRotate_idxFree (d s : LOperand) (opn mov : String)
    (hs : noIdxB s = true) : ∀ r ∈ lowerNativeShiftRotate d s opn mov, idxFreeB r = true := by
  unfold lowerNativeShiftRotate
  split <;> simp [idxFreeB, hs]

theorem legalizeOneSrc_idxFree (u64 : Bool) (opn : String) (d s : LOperand)
    (hs : noIdxB s = true) :
    ∀ r ∈ legalizeOneSrc u64 opn d s, idxFreeB r = true := by
  unfold legalizeOneSrc
  split
  · exact legalizeMov_idxFree d s _ hs
  · simp [idxFreeB, hs]

theorem legalizeSpillDst_idxFree (dsts : List LOperand) (opn : String) (srcs : List LOperand)
    (hs : ∀ x ∈ srcs, noIdxB x = true) :
    ∀ r ∈ legalizeSpillDst dsts opn srcs, idxFreeB r = true := by
  unfold legalizeSpillDst
  split
  · next l h =>
    unfold cmovSpillDst? at h
    split at h
    · split at h
      · cases h
        unfold cmovSpillSeq
        split_ifs <;> simp_all [idxFreeB]
      · cases h
    · cases h
  · split
    · next l _ h =>
      unfold setccSpill? at h
      split at h
      · split at h
        · cases h
          simp_all [idxFreeB]
        · cases h
      · cases h
    · simpa [idxFreeB] using hs

theorem legalizeSibElem_of_noIdx {o : LOperand} (h : noIdxB o = true) :
    legalizeSibElem o = ([], o) := by
  cases o <;> simp_all [legalizeSibElem, noIdxB]

theorem reloadMemrefBase_of_noIdx (mbr : String → Option String) {o : LOperand}
    (h : noIdxB o = true) : reloadMemrefBase mbr o = ([], o) := by
  cases o <;> simp_all [reloadMemrefBase, noIdxB]

theorem legalizeMemLoad_idxFree (d s : LOperand) (opn mov : String) (hs : noIdxB s = true) :
    ∀ r ∈ legalizeMemLoad d s opn mov, idxFreeB r = true := by
  unfold legalizeMemLoad
  rw [legalizeSibElem_of_noIdx hs]
  simp only [List.nil_append]
  split <;> simp [idxFreeB, hs]

theorem legalizeMemStoreK_idxFree (k : Option Nat) (dArr addr val : LOperand)
    (opn mov : String) (ha : noIdxB addr = true) (hv : noIdxB val = true) :
    ∀ r ∈ legalizeMemStoreK k dArr addr val opn mov, idxFreeB r = true := by
  have hc : constIdxStore? k addr val = none :=
    constIdxStore?_of_not_arrIdx k val (fun b i sc he => by subst he; simp [noIdxB] at ha)
  rw [legalizeMemStoreK_of_none dArr opn mov hc]
  unfold legalizeMemStore
  rw [legalizeSibElem_of_noIdx ha]
  simp only [List.nil_append]
  split
  · simp [noIdxB] at ha
  · simp [idxFreeB, ha, hv]
  · simp [idxFreeB, ha, hv]

theorem noIdxB_remapOperand (body : Lcmd) (tbl : Array Nat) {x : LOperand}
    (h : noIdxB x = true) : noIdxB (remapOperand body tbl x) = true := by
  cases x <;> simp_all [remapOperand, noIdxB]

/-- **An expansion without indexed operand.** The expansion `physExpand` of an instruction
    none of whose operands is register-indexed, under an operand map that keeps operands
    without index, has no register-indexed source. -/
theorem physExpand_idxFree (shiftImm : ShiftImmOracle) (u64 : Bool)
    (rmap : LOperand → LOperand) (mbr : String → Option String) (i : Linstr)
    (hrm : ∀ x, noIdxB x = true → noIdxB (rmap x) = true)
    (h : ∀ x ∈ lopnOperands i.li_i, noIdxB x = true) :
    ∀ r ∈ physExpand shiftImm u64 rmap mbr i, idxFreeB r.li_i = true := by
  obtain ⟨ii, w⟩ := i
  have hmap : ∀ (P : LinstrR → Prop) (l : List LinstrR), (∀ r ∈ l, P r) →
      ∀ r ∈ l.map (fun r => (⟨ii, r⟩ : Linstr)), P r.li_i := by
    intro P l hl r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    exact hl r' hr'
  cases w with
  | Lopn ds o ss =>
    have hx : ∀ x ∈ ds ++ ss, noIdxB (rmap x) = true :=
      fun x hx' => hrm x (h x (by simpa [lopnOperands] using hx'))
    simp only [List.mem_append] at hx
    unfold physExpand
    dsimp only
    split
    · rename_i d _ opn s0 s1 _ heq
      cases heq
      have hd := hx d (Or.inl List.mem_cons_self)
      have h0 := hx s0 (Or.inr List.mem_cons_self)
      have h1 := hx s1 (Or.inr (by simp))
      split
      · split
        · exact hmap _ _ (lowerTwoAddrShiftImm_idxFree _ _ _ _ _ hd h0)
        · exact hmap _ _ (lowerTwoAddr_idxFree _ _ _ _ _ hd h0 h1)
      · split
        · rename_i d' opn' addr val heq
          cases heq
          split
          · rw [reloadMemrefBase_of_noIdx mbr h0]
            simp only [List.map_nil, List.nil_append]
            exact hmap _ _ (legalizeMemStoreK_idxFree _ _ _ _ _ _ h0 h1)
          · exact hmap _ _ (legalizeSpillDst_idxFree _ _ _ (by simp [h0, h1]))
        · rename_i heq
          cases heq
          exact hmap _ _ (legalizeSpillDst_idxFree _ _ _
            (fun x hx' => by
              obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx'
              exact hx y (Or.inr hy)))
        · rename_i hno
          exact absurd rfl (hno _ _ _)
    · rename_i d opn s heq
      cases heq
      have hd := hx d (Or.inl List.mem_cons_self)
      have hs := hx s (Or.inr List.mem_cons_self)
      split
      · exact hmap _ _ (lowerNativeShiftRotate_idxFree _ _ _ _ hs)
      · split
        · rw [reloadMemrefBase_of_noIdx mbr hs]
          simp only [List.map_nil, List.nil_append]
          exact hmap _ _ (legalizeMemLoad_idxFree _ _ _ _ hs)
        · exact hmap _ _ (legalizeOneSrc_idxFree _ _ _ _ hs)
    · rename_i dsts opn srcs _ _ heq
      cases heq
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [idxFreeB, List.all_eq_true, List.mem_map]
      rintro _ ⟨y, hy, rfl⟩
      exact hx y (Or.inr hy)
    · rename_i hno
      exact absurd rfl (hno _ _ _)
  | _ =>
    intro r hr
    simp only [physExpand, List.mem_singleton] at hr
    subst hr; rfl

/-! ## 5. The reload windows of the access arms -/

/-- The instruction passes the reload scan of `x`: an operation none of whose destinations
    names `x` or an array slot. -/
def PassesB (slotArr : String → Option (String × Nat)) (x : String) (r : LinstrR) : Prop :=
  ∃ ds o ss, r = .Lopn ds o ss ∧ ds.any (dstHitB slotArr x) = false

theorem scanExit_succ_pass {c : Lcmd} {k : Nat} {j : Linstr} {x : String}
    (hk : c[k]? = some j) (hp : PassesB slotArr x j.li_i) :
    scanExit slotArr c (k + 1) x = scanExit slotArr c k x := by
  obtain ⟨ds, o, ss, he, hd⟩ := hp
  simp only [scanExit, hk]
  cases hm : slotMov? j.li_i with
  | some p =>
    obtain ⟨d, q⟩ := p
    obtain ⟨o', ho⟩ := slotMov?_eq hm
    rw [ho] at he
    cases he
    simp only [List.any_cons, List.any_nil, Bool.or_false, dstHitB, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq] at hd
    simp only [hd.1, if_false]
    simp at hd
    simp [hd.2]
  | none =>
    simp only
    rw [he]
    simp [hd]

/-- **A reload window keeps its scans.** A block that starts with a move of the slot `q` of an
    array into `R14`, continues with operations that pass the scan of `R14` and have no
    indexed source, then has one instruction whose indexed first source at stride `8` is
    based at `R14`, then only instructions without indexed source, keeps its scans. -/
theorem scanStays_window {rl acc : Linstr} {mid post : Lcmd} {q : String}
    (hrl : slotMov? rl.li_i = some (reloadScratch2, q)) (hq : (slotArr q).isSome = true)
    (hmid : ∀ r ∈ mid, PassesB slotArr reloadScratch2 r.li_i ∧ idxFreeB r.li_i = true)
    (hacc : ∀ ds o x y ss, acc.li_i = .Lopn ds o (.arrIdx x y 8 :: ss) → x = reloadScratch2)
    (hpost : ∀ r ∈ post, idxFreeB r.li_i = true) :
    ScanStays slotArr (rl :: (mid ++ acc :: post)) := by
  have hrlI : idxFreeB rl.li_i = true := by
    obtain ⟨o, ho⟩ := slotMov?_eq hrl
    rw [ho]; rfl
  intro k i hk ds o x y ss hx
  have hvac : idxFreeB i.li_i = true → False := fun h => by
    rw [hx] at h; simp [idxFreeB] at h
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk; exact (hvac hrlI).elim
  | succ k =>
    simp only [List.getElem?_cons_succ] at hk
    rcases Nat.lt_trichotomy k mid.length with hlt | heq | hgt
    · rw [List.getElem?_append_left hlt] at hk
      exact (hvac (hmid _ (List.mem_of_getElem? hk)).2).elim
    · subst heq
      rw [List.getElem?_append_right (by omega), Nat.sub_self] at hk
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      have hx14 := hacc ds o x y ss hx
      subst hx14
      have hpass : ∀ m, m ≤ mid.length → scanExit slotArr (rl :: (mid ++ acc :: post)) (m + 1)
          reloadScratch2 = none := by
        intro m
        induction m with
        | zero =>
          intro _
          simp only [scanExit, List.getElem?_cons_zero, hrl, if_true]
          simp [Option.isSome_iff_ne_none] at hq
          simp [hq]
        | succ m ih =>
          intro hm
          have hg : (rl :: (mid ++ acc :: post))[m + 1]? = mid[m]? := by
            simp only [List.getElem?_cons_succ, List.getElem?_append_left (by omega : m < mid.length)]
          obtain ⟨r, hr⟩ : ∃ r, mid[m]? = some r :=
            ⟨mid[m], List.getElem?_eq_getElem (by omega)⟩
          rw [scanExit_succ_pass (hg.trans hr) (hmid r (List.mem_of_getElem? hr)).1]
          exact ih (by omega)
      exact hpass _ le_rfl
    · rw [List.getElem?_append_right (by omega)] at hk
      obtain ⟨m, hm⟩ : ∃ m, k - mid.length = m + 1 := ⟨k - mid.length - 1, by omega⟩
      rw [hm, List.getElem?_cons_succ] at hk
      exact (hvac (hpost _ (List.mem_of_getElem? hk))).elim

theorem passes_mov_r15 (hs15 : slotArr reloadScratch = none) (o : String) (ss : List LOperand) :
    PassesB slotArr reloadScratch2 (.Lopn [.reg reloadScratch] o ss) :=
  ⟨_, _, _, rfl, by simp [dstHitB_r15_r14 hs15]⟩

/-- **The load arm keeps its scans.** The reload `MOVQ R14, q` of the slot of an array
    followed by `legalizeMemLoad` of an `LOADIDX` from `R14` at stride `8` keeps its scans. -/
theorem loadIdx_scanStays (hs15 : slotArr reloadScratch = none) {q : String}
    (hq : (slotArr q).isSome = true) (ii : Nat) (d : LOperand) (n y mov : String)
    (hd : d = .reg n) :
    ScanStays slotArr (([LinstrR.Lopn [.reg reloadScratch2] "MOVQ" [.reg q]].map
        (fun r => (⟨ii, r⟩ : Linstr))) ++
      (legalizeMemLoad d (.arrIdx reloadScratch2 y 8) "LOADIDX" mov).map
        (fun r => (⟨ii, r⟩ : Linstr))) := by
  subst hd
  have hrl : slotMov? (LinstrR.Lopn [.reg reloadScratch2] "MOVQ" [.reg q])
      = some (reloadScratch2, q) := by simp [slotMov?]
  simp only [legalizeMemLoad, legalizeSibElem, sibNameSpill_reloadScratch2]
  cases hy : sibNameSpill y <;> cases hn : (LOperand.reg n).isSpill <;>
    simp only [Bool.false_eq_true, if_false, if_true, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, ge_iff_le, Nat.le_refl]
  · exact scanStays_window (mid := []) (post := []) hrl hq (by simp)
      (fun _ _ _ _ _ h => by cases h; rfl) (by simp)
  · exact scanStays_window (mid := []) hrl hq (by simp)
      (fun _ _ _ _ _ h => by cases h; rfl) (by simp [idxFreeB])
  · exact scanStays_window (mid := [_]) (post := []) hrl hq
      (by simp [idxFreeB, passes_mov_r15 hs15])
      (fun _ _ _ _ _ h => by cases h; rfl) (by simp)
  · exact scanStays_window (mid := [_]) hrl hq
      (by simp [idxFreeB, passes_mov_r15 hs15])
      (fun _ _ _ _ _ h => by cases h; rfl) (by simp [idxFreeB])

/-- **The store arm keeps its scans.** The reload `MOVQ R14, q` of the slot of an array
    followed by `legalizeMemStoreK` of an `STOREIDX` of a register to `R14` at stride `8`
    keeps its scans. -/
theorem storeIdx_scanStays (hs15 : slotArr reloadScratch = none) {q : String}
    (hq : (slotArr q).isSome = true) (ii : Nat) (kc : Option Nat) (dA val : LOperand)
    (na y v mov : String) (hda : dA = .reg na) (hv : val = .reg v) :
    ScanStays slotArr (([LinstrR.Lopn [.reg reloadScratch2] "MOVQ" [.reg q]].map
        (fun r => (⟨ii, r⟩ : Linstr))) ++
      (legalizeMemStoreK kc dA (.arrIdx reloadScratch2 y 8) val "STOREIDX" mov).map
        (fun r => (⟨ii, r⟩ : Linstr))) := by
  subst hda hv
  have hrl : slotMov? (LinstrR.Lopn [.reg reloadScratch2] "MOVQ" [.reg q])
      = some (reloadScratch2, q) := by simp [slotMov?]
  cases hc : constIdxStore? kc (.arrIdx reloadScratch2 y 8) (.reg v) with
  | some l =>
    simp only [legalizeMemStoreK, hc]
    refine scanStays_of_idxFree ?_
    intro r hr
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | ⟨r', hr', rfl⟩
    · rfl
    · unfold constIdxStore? at hc
      simp only at hc
      split_ifs at hc
      all_goals
        split at hc
        · split_ifs at hc
          cases hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
          rcases hr' with h | h | h <;> (try subst h) <;>
            first | exact h.elim | simp [idxFreeB]
        · cases hc
  | none =>
    rw [legalizeMemStoreK_of_none _ _ _ hc]
    simp only [legalizeMemStore, legalizeSibElem, sibNameSpill_reloadScratch2]
    cases hy : sibNameSpill y <;> cases hn : (LOperand.reg v).isSpill <;>
      simp only [Bool.false_eq_true, if_false, if_true, List.nil_append, List.cons_append,
        List.map_cons, List.map_nil, ge_iff_le, Nat.le_refl, beq_self_eq_true]
    · exact scanStays_window (mid := []) (post := []) hrl hq (by simp)
        (fun _ _ _ _ _ h => by cases h; rfl) (by simp)
    · split
      · exact scanStays_window (mid := []) hrl hq (by simp)
          (fun _ _ _ _ _ h => by cases h; rfl) (by simp [idxFreeB])
      · exact scanStays_window (mid := [_]) (post := []) hrl hq
          (by simp [idxFreeB, passes_mov_r15 hs15])
          (fun _ _ _ _ _ h => by cases h; rfl) (by simp)
    · exact scanStays_window (mid := [_]) (post := []) hrl hq
        (by simp [idxFreeB, passes_mov_r15 hs15])
        (fun _ _ _ _ _ h => by cases h; rfl) (by simp)
    · exact scanStays_window (mid := [_]) (post := [_, _]) hrl hq
        (by simp [idxFreeB, passes_mov_r15 hs15])
        (fun _ _ _ _ _ h => by cases h; rfl) (by simp [idxFreeB])

/-! ## 6. The home condition -/

/-- The instruction is no low `MUL` of the form `homeOkB` checks. -/
def noLowMulB : LinstrR → Bool
  | .Lopn [.reg _] opn [.reg _, .reg _] => !isLowMulMnem opn
  | _ => true

theorem homeOkB_cons_of_noLowMul {i : Linstr} (h : noLowMulB i.li_i = true) (env : ScratchEnv)
    (rest : Lcmd) : homeOkB slotArr env (i :: rest) = homeOkB slotArr (scratchStep env i) rest := by
  simp only [homeOkB]
  split
  · rename_i heq
    rw [heq] at h
    simp only [noLowMulB, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    simp [h]
  · simp

theorem homeOkB_append (env : ScratchEnv) : ∀ (a c : Lcmd),
    homeOkB slotArr env (a ++ c) =
      (homeOkB slotArr env a && homeOkB slotArr (a.foldl scratchStep env) c)
  | [], c => by simp [homeOkB]
  | i :: a, c => by
    simp only [List.cons_append, homeOkB, List.foldl_cons, Bool.and_assoc]
    rw [homeOkB_append (scratchStep env i) a c]

theorem envScratch_foldl {env : ScratchEnv} (h : EnvScratch env) :
    ∀ xs : Lcmd, EnvScratch (xs.foldl scratchStep env)
  | [] => h
  | i :: xs => envScratch_foldl (h.step i) xs

theorem homeOkB_of_noLowMul : ∀ {c : Lcmd}, (∀ r ∈ c, noLowMulB r.li_i = true) →
    ∀ env, homeOkB slotArr env c = true
  | [], _, _ => rfl
  | i :: c, h, env => by
    rw [homeOkB_cons_of_noLowMul (h i List.mem_cons_self)]
    exact homeOkB_of_noLowMul (fun r hr => h r (List.mem_cons_of_mem _ hr)) _

theorem homeOkB_flatMap {α : Type} {l : List α} {f : α → Lcmd}
    (h : ∀ a ∈ l, ∀ env, EnvScratch env → homeOkB slotArr env (f a) = true) :
    ∀ env, EnvScratch env → homeOkB slotArr env (l.flatMap f) = true := by
  induction l with
  | nil => intro _ _; rfl
  | cons a l ih =>
    intro env he
    rw [List.flatMap_cons, homeOkB_append, h a List.mem_cons_self env he, Bool.true_and]
    exact ih (fun a' ha' => h a' (List.mem_cons_of_mem a ha')) _ (envScratch_foldl he _)

theorem homeOkB_dropLast {l : Lcmd} {env : ScratchEnv} (h : homeOkB slotArr env l = true) :
    homeOkB slotArr env l.dropLast = true := by
  have hl : l = l.dropLast ++ l.drop (l.length - 1) := by
    rw [List.dropLast_eq_take, List.take_append_drop]
  rw [hl, homeOkB_append, Bool.and_eq_true] at h
  exact h.1

/-- No register name of the x86 allocation is a reload scratch. -/
theorem physRegName_not_scratch (p : Nat) : physRegName p x86Abi ∉ fuseReloadScratches := by
  have hk : ∀ (a s : String) (c : Char), a.toList.head? = some c → c ≠ 'R' →
      a ++ s ∉ fuseReloadScratches := by
    intro a s c ha hc hm
    obtain ⟨t, ht⟩ : ∃ t, a.toList = c :: t := by
      cases hl : a.toList with
      | nil => rw [hl] at ha; cases ha
      | cons c' t => rw [hl] at ha; cases ha; exact ⟨t, rfl⟩
    have e15 : reloadScratch.toList = ['R', '1', '5'] := by decide +kernel
    have e14 : reloadScratch2.toList = ['R', '1', '4'] := by decide +kernel
    simp only [fuseReloadScratches, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h <;> have := congrArg String.toList h <;>
      rw [String.toList_append, ht] at this
    · rw [e15] at this; exact hc (List.cons.inj this).1
    · rw [e14] at this; exact hc (List.cons.inj this).1
  unfold physRegName
  split
  · dsimp only
    split
    · next r hr =>
      have hall : ∀ r ∈ vectorRegNames, r ∉ fuseReloadScratches := by decide +kernel
      exact hall r (List.mem_of_getElem? hr)
    · exact hk "kv." _ 'k' (by decide +kernel) (by decide)
  · split
    · next r hr =>
      have hall : ∀ r ∈ x86Abi.allocPool, r ∉ fuseReloadScratches := by decide +kernel
      exact hall r (List.mem_of_getElem? hr)
    · exact hk "k." _ 'k' (by decide +kernel) (by decide)

/-- After a move of `x` into `R15`, the scratch `R15` resolves to `R15` or to the register `x`
    names, when that register is no reload scratch. -/
theorem slotArr_resolve_mov_r15 (hs15 : slotArr reloadScratch = none) {env : ScratchEnv}
    (he : EnvScratch env) (ii : Nat) (mov : String) (x : LOperand)
    (hx : ∀ n, x = .reg n → n ∉ fuseReloadScratches ∧ slotArr n = none) :
    slotArr (scratchResolve (scratchStep env ⟨ii, .Lopn [.reg reloadScratch] mov [x]⟩)
      reloadScratch) = none := by
  have h15 : reloadScratch ∈ fuseReloadScratches := by simp [fuseReloadScratches]
  rw [(scratchResolve_scratchStep env _ reloadScratch).1 _ _ _ rfl List.mem_cons_self h15]
  unfold stepVal
  split
  · rename_i sn hsn
    obtain ⟨h1, h2⟩ := hx sn (by simpa using hsn)
    split
    · rw [scratchResolve_of_envScratch he h1]; exact h2
    · exact hs15
  · exact hs15

/-- **The home condition on the two-address lowering of a low `MUL`.** If the destination is
    a register, let it be no reload scratch and no array slot. Then the lowering satisfies
    `homeOkB` from every environment that records only reload scratches: each low `MUL` it
    emits writes the destination, or `R15` after the move of the destination into `R15`. -/
theorem homeOkB_lowerTwoAddr (hs15 : slotArr reloadScratch = none) (ii : Nat)
    (d s0 s1 : LOperand) (opn mov : String)
    (hd : ∀ n, d = .reg n → n ∉ fuseReloadScratches ∧ slotArr n = none)
    (env : ScratchEnv) (he : EnvScratch env) :
    homeOkB slotArr env ((lowerTwoAddr d s0 s1 opn mov).map (fun r => (⟨ii, r⟩ : Linstr)))
      = true := by
  have hsingle : ∀ (l : List LinstrR), (∀ r ∈ l, ∃ ds o s, r = .Lopn ds o [s]) →
      ∀ r ∈ l.map (fun r => (⟨ii, r⟩ : Linstr)), noLowMulB r.li_i = true := by
    intro l hl r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    obtain ⟨ds, o, s, rfl⟩ := hl r' hr'
    simp only [noLowMulB]
  have hbin : ∀ (s : LOperand) (env : ScratchEnv), EnvScratch env →
      homeOkB slotArr env ((legalizeBinop d s opn mov).map
        (fun r => (⟨ii, r⟩ : Linstr))) = true := by
    intro s env he
    have hdst : ∀ (env' : ScratchEnv), EnvScratch env' → ∀ (t : LOperand),
        homeOkB slotArr env' [⟨ii, .Lopn [d] opn [d, t]⟩] = true := by
      intro env' he' t
      simp only [homeOkB, Bool.and_true]
      split
      · rename_i dn _ _ _ heq
        injection heq with h1 _ _
        simp only [List.cons.injEq, and_true] at h1
        obtain ⟨hn1, hn2⟩ := hd dn h1
        simp [hn2, scratchResolve_of_envScratch he' hn1]
      · rfl
    have hr15 : ∀ (env' : ScratchEnv), EnvScratch env' → ∀ (t : LOperand),
        slotArr (scratchResolve env' reloadScratch) = none →
        homeOkB slotArr env' [⟨ii, .Lopn [.reg reloadScratch] opn [.reg reloadScratch, t]⟩]
          = true := by
      intro env' _ t hres
      simp only [homeOkB, Bool.and_true]
      split
      · rename_i dn _ _ _ heq
        injection heq with h1 _ _
        simp only [List.cons.injEq, LOperand.reg.injEq, and_true] at h1
        subst h1
        simp [hs15, hres]
      · rfl
    unfold legalizeBinop
    split
    · simp only [List.map_cons, List.map_nil]
      exact hdst env he s
    · simp only [List.map_cons, List.map_nil]
      rw [homeOkB_cons_of_noLowMul (by simp [noLowMulB])]
      exact hdst _ (he.step _) _
    · simp only [List.map_cons, List.map_nil]
      rw [homeOkB_cons_of_noLowMul (by simp [noLowMulB])]
      rw [show ∀ (a b : Linstr) (e : ScratchEnv), homeOkB slotArr e [a, b] =
          (homeOkB slotArr e [a] && homeOkB slotArr (scratchStep e a) [b]) from
        fun a b e => homeOkB_append e [a] [b]]
      rw [hr15 _ (he.step _) s (slotArr_resolve_mov_r15 hs15 he ii mov d hd), Bool.true_and]
      exact homeOkB_of_noLowMul (by simp [noLowMulB]) _
    · simp only [List.map_cons, List.map_nil]
      rw [homeOkB_cons_of_noLowMul (by simp [noLowMulB])]
      rw [homeOkB_cons_of_noLowMul (by simp [noLowMulB])]
      rw [show ∀ (a b : Linstr) (e : ScratchEnv), homeOkB slotArr e [a, b] =
          (homeOkB slotArr e [a] && homeOkB slotArr (scratchStep e a) [b]) from
        fun a b e => homeOkB_append e [a] [b]]
      have hres : slotArr (scratchResolve (scratchStep (scratchStep env
          ⟨ii, .Lopn [.reg reloadScratch] mov [d]⟩)
          ⟨ii, .Lopn [.reg reloadScratch2] mov [s]⟩) reloadScratch) = none := by
        rw [(scratchResolve_scratchStep _ _ reloadScratch).2 (fun ds o ss heq hm => by
          cases heq
          simp only [List.mem_singleton, LOperand.reg.injEq] at hm
          exact absurd hm.1 (by decide +kernel))]
        exact slotArr_resolve_mov_r15 hs15 he ii mov d hd
      rw [hr15 _ ((he.step _).step _) _ hres, Bool.true_and]
      exact homeOkB_of_noLowMul (by simp [noLowMulB]) _
  unfold lowerTwoAddr
  rcases hmw : materializeWideImm s1 mov with ⟨pre, s1v⟩
  have hpreS : ∀ r ∈ pre, ∃ ds o s, r = .Lopn ds o [s] := by
    intro r hr
    unfold materializeWideImm at hmw
    split at hmw
    · split at hmw <;> cases hmw
      · simp at hr; subst hr; exact ⟨_, _, _, rfl⟩
      · simp at hr
    · cases hmw; simp at hr
  simp only
  split
  · rw [List.map_append, homeOkB_append,
      homeOkB_of_noLowMul (hsingle pre hpreS), Bool.true_and]
    exact hbin _ _ (envScratch_foldl he _)
  · have hmov : ∀ r ∈ legalizeMov d s0 mov, ∃ ds o s, r = .Lopn ds o [s] := by
      unfold legalizeMov
      split <;> simp
    rw [List.map_append, List.map_append, homeOkB_append, homeOkB_append,
      homeOkB_of_noLowMul (hsingle _ hmov), homeOkB_of_noLowMul (hsingle pre hpreS),
      Bool.true_and, Bool.true_and]
    exact hbin _ _ (envScratch_foldl he _)

/-! ## 7. One expansion -/

theorem isMnem_mul {o : String} (h : stripWidthTag o = "MUL") :
    isTwoAddrBinop o = true ∧ (stripWidthTag o == "SHL" || stripWidthTag o == "SHR") = false ∧
      isNativeShiftRotate o = false ∧ isMemLoad o = false ∧ isMemStore o = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [isTwoAddrBinop, h]; decide
  · rw [h]; decide
  · simp only [isNativeShiftRotate, h, PhysAbiShape.isPrefixOf_eq_list]; decide +kernel
  · simp only [isMemLoad, h]; decide
  · simp only [isMemStore, h]; decide

/-- **The home condition on the expansion of a low `MUL`.** Under an operand map whose register
    images are no reload scratches and no array slots, the expansion of an instruction with a
    low `MUL` mnemonic satisfies `homeOkB` from every environment that records only reload
    scratches. -/
theorem physExpand_lowMul_homeOkB (hs15 : slotArr reloadScratch = none)
    (shiftImm : ShiftImmOracle) (u64 : Bool) (rmap : LOperand → LOperand)
    (mbr : String → Option String) (ii : Nat) (ds : List LOperand) (o : String)
    (ss : List LOperand) (hlow : stripWidthTag o = "MUL")
    (hrm : ∀ x n, rmap x = .reg n → n ∉ fuseReloadScratches ∧ slotArr n = none)
    (env : ScratchEnv) (he : EnvScratch env) :
    homeOkB slotArr env (physExpand shiftImm u64 rmap mbr ⟨ii, .Lopn ds o ss⟩) = true := by
  obtain ⟨hbin, hsh, hnat, hml, -⟩ := isMnem_mul hlow
  have hm1 : stripWidthTag o ≠ "MOV" := by rw [hlow]; decide
  have hm2 : stripWidthTag o ≠ "MOVQ" := by rw [hlow]; decide
  rcases ds with _ | ⟨d, ds⟩
  · refine homeOkB_of_noLowMul ?_ _
    rcases ss with _ | ⟨s0, _ | ⟨s1, ss⟩⟩ <;> simp [physExpand, noLowMulB]
  · rcases ss with _ | ⟨s0, _ | ⟨s1, ss⟩⟩
    · refine homeOkB_of_noLowMul ?_ _
      simp [physExpand, noLowMulB]
    · refine homeOkB_of_noLowMul ?_ _
      rcases ds with _ | ⟨d2, ds⟩
      · simp [physExpand, hnat, hml, legalizeOneSrc_of_ne _ _ hm1 hm2, noLowMulB]
      · simp [physExpand, noLowMulB]
    · simp only [physExpand, hbin, if_true, hsh, Bool.false_eq_true, if_false]
      exact homeOkB_lowerTwoAddr hs15 ii _ _ _ _ _ (fun n h => hrm d n h) env he

/-- An instruction of no virtual mnemonic but `o`, and no move mnemonic. -/
def MnemOk (i : LinstrR) (L : Lcmd) : Prop :=
  ∀ r ∈ L, ∀ ds o ss, r.li_i = .Lopn ds o ss → some o = opnOf i ∨ o ∈ movMnems

theorem movMnems_not_mulHi : ∀ o ∈ movMnems, isMulHiMnem o = false := by decide +kernel

theorem movMnems_not_lowMul : ∀ o ∈ movMnems, isLowMulMnem o = false := by decide +kernel

theorem filter_notLivePin_eq {i : LinstrR} {L : Lcmd} (h : MnemOk i L)
    (hl : opnOf i ≠ some "LIVEPIN") : L.filter notLivePin = L := by
  refine List.filter_eq_self.mpr fun r hr => ?_
  unfold notLivePin
  split
  · rename_i ds o ss he
    simp only [bne_iff_ne, ne_eq]
    rcases h r hr ds o ss he with ho | ho
    · rintro rfl; exact hl ho.symm
    · exact movMnems_ne_livepin ho
  · rfl

theorem noSite_of_mnemOk {i : LinstrR} {L : Lcmd} (h : MnemOk i L)
    (hi : ∀ o, opnOf i = some o → isMulHiMnem o = false) : ∀ r ∈ L, mulHiSiteB r = false := by
  intro r hr
  unfold mulHiSiteB
  split
  · rename_i a opn b c he
    rcases h r hr _ _ _ he with ho | ho
    · exact hi opn ho.symm
    · exact movMnems_not_mulHi opn ho
  · rfl

theorem noLowMul_of_mnemOk {i : LinstrR} {L : Lcmd} (h : MnemOk i L)
    (hi : ∀ o, opnOf i = some o → isLowMulMnem o = false) :
    ∀ r ∈ L, noLowMulB r.li_i = true := by
  intro r hr
  cases he : r.li_i with
  | Lopn ds o ss =>
    have ho : isLowMulMnem o = false := by
      rcases h r hr ds o ss he with ho | ho
      · exact hi o ho.symm
      · exact movMnems_not_lowMul o ho
    unfold noLowMulB
    split
    · rename_i heq; cases heq; simp [ho]
    · rfl
  | _ => rfl

theorem isMulHiMnem_acc (o : String) (h : o = "LOADIDX" ∨ o = "STOREIDX") :
    isMulHiMnem o = false ∧ isLowMulMnem o = false ∧ o ≠ "LIVEPIN" := by
  rcases h with rfl | rfl <;> decide +kernel

/-- **One expansion keeps the side conditions.** Let the expansion of `i` carry only its own
    mnemonic and moves, let the operand map send registers to registers that are no reload
    scratches and no array slots and keep operands without index, let `i` have the access
    form, and let `i` have no indexed operand when it is no access. Then the expansion without
    its `LIVEPIN` instructions keeps its scans, keeps the scans of every suffix behind a site,
    and satisfies `homeOkB` from every environment that records only reload scratches. -/
theorem physExpand_block (hs15 : slotArr reloadScratch = none)
    (shiftImm : ShiftImmOracle) (u64 : Bool) (rmap : LOperand → LOperand)
    (mbr : String → Option String) (i : Linstr)
    (hmn : MnemOk i.li_i (physExpand shiftImm u64 rmap mbr i))
    (hrmI : ∀ x, noIdxB x = true → noIdxB (rmap x) = true)
    (hrmR : ∀ x n, rmap x = .reg n → n ∉ fuseReloadScratches ∧ slotArr n = none)
    (hreg : ∀ n, ∃ n', rmap (.reg n) = .reg n')
    (hacc : AccForm slotArr rmap mbr i.li_i)
    (hidx : isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true) :
    let F := (physExpand shiftImm u64 rmap mbr i).filter notLivePin
    ScanStays slotArr F ∧ SiteStays slotArr F ∧
      ∀ env, EnvScratch env → homeOkB slotArr env F = true := by
  intro F
  have hsub : ∀ r ∈ F, r ∈ physExpand shiftImm u64 rmap mbr i := fun r hr =>
    List.mem_of_mem_filter hr
  cases hA : isAccB i.li_i
  · -- no access: no indexed operand
    have hfree : ∀ r ∈ F, idxFreeB r.li_i = true := fun r hr =>
      physExpand_idxFree shiftImm u64 rmap mbr i hrmI (hidx hA) r (hsub r hr)
    refine ⟨scanStays_of_idxFree hfree, siteStays_of_idxFree hfree, fun env he => ?_⟩
    by_cases hlow : ∃ ds o ss, i.li_i = .Lopn ds o ss ∧ stripWidthTag o = "MUL"
    · obtain ⟨ds, o, ss, hi, hm⟩ := hlow
      have hF : F = physExpand shiftImm u64 rmap mbr i := by
        refine filter_notLivePin_eq hmn ?_
        rw [hi]
        rintro ⟨⟩
        revert hm; decide +kernel
      rw [hF]
      obtain ⟨ii, w⟩ := i
      simp only at hi
      subst hi
      exact physExpand_lowMul_homeOkB hs15 shiftImm u64 rmap mbr ii ds o ss hm hrmR env he
    · refine homeOkB_of_noLowMul (fun r hr => noLowMul_of_mnemOk hmn ?_ r (hsub r hr)) _
      intro o ho
      cases hw : i.li_i with
      | Lopn ds o' ss =>
        rw [hw] at ho
        cases ho
        simp only [isLowMulMnem, beq_eq_false_iff_ne, ne_eq]
        exact fun hm => hlow ⟨ds, o, ss, hw, hm⟩
      | _ => rw [hw] at ho; cases ho
  · -- an access
    obtain ⟨ii, w⟩ := i
    simp only at hA hacc hmn ⊢
    cases w with
    | Lopn ds o ss =>
      have ho : o = "LOADIDX" ∨ o = "STOREIDX" := by
        simpa [isAccB] using hA
      obtain ⟨hmh, hml, hlp⟩ := isMulHiMnem_acc o ho
      have hF : F = physExpand shiftImm u64 rmap mbr ⟨ii, .Lopn ds o ss⟩ :=
        filter_notLivePin_eq hmn (by simpa [opnOf] using hlp)
      have hns : ∀ r ∈ F, mulHiSiteB r = false := fun r hr =>
        noSite_of_mnemOk hmn (fun o' h' => by cases h'; exact hmh) r (hsub r hr)
      have hnm : ∀ r ∈ F, noLowMulB r.li_i = true := fun r hr =>
        noLowMul_of_mnemOk hmn (fun o' h' => by cases h'; exact hml) r (hsub r hr)
      refine ⟨?_, SiteStays.of_noSite hns, fun env _ => homeOkB_of_noLowMul hnm env⟩
      rw [hF]
      obtain ⟨hL, hS, -⟩ := hacc ds o ss rfl
      rcases ho with rfl | rfl
      · obtain ⟨dn, b, y, rfl, rfl, b', y', q, hrmA, hmb, hq⟩ := hL rfl
        obtain ⟨n', hn'⟩ := hreg dn
        simp only [physExpand, isNativeShiftRotate_loadIdx, isMemLoad_loadIdx,
          Bool.false_eq_true, if_false, if_true, hrmA, hn', reloadMemrefBase, hmb]
        exact loadIdx_scanStays hs15 hq ii _ n' y' _ rfl
      · obtain ⟨dn, b, y, v, rfl, rfl, b', y', q, hrmA, hmb, hq⟩ := hS rfl
        obtain ⟨n', hn'⟩ := hreg dn
        obtain ⟨v', hv'⟩ := hreg v
        simp only [physExpand, isTwoAddrBinop_storeIdx, isMemStore_storeIdx,
          Bool.false_eq_true, if_false, if_true, hrmA, hn', hv', reloadMemrefBase, hmb]
        exact storeIdx_scanStays hs15 hq ii _ _ _ n' y' v' _ rfl rfl
    | _ => simp [isAccB] at hA

/-! ## 8. The export -/

/-- The instruction is no site, has no indexed source and is no low `MUL`. -/
def PlainB (r : Linstr) : Prop :=
  mulHiSiteB r = false ∧ idxFreeB r.li_i = true ∧ noLowMulB r.li_i = true

theorem plainB_of_mov {r : Linstr} {d o s : String} (h : r.li_i = .Lopn [.reg d] o [.reg s]) :
    PlainB r := by
  unfold PlainB mulHiSiteB idxFreeB noLowMulB
  rw [h]
  simp

theorem plainB_ret : PlainB ⟨0, .Lret⟩ := ⟨rfl, rfl, rfl⟩

theorem prologue_plainB (virt : Lfundef) (tbl : Array Nat) (abiArgs : List String) :
    ∀ r ∈ buildPrologue virt tbl (fun _ => none) ++ extraSaves abiArgs, PlainB r := by
  intro r hr
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ((prologue_moves virt tbl abiArgs).1 r hr)
  obtain ⟨o, ho⟩ := slotMov?_eq hp
  exact plainB_of_mov ho

theorem buildArgPtrMaterialize_plainB (virt : Lfundef) (tbl : Array Nat)
    (abiArgs : List String) (inLoadMap : InLoadMap) :
    ∀ r ∈ buildArgPtrMaterialize virt tbl abiArgs inLoadMap, PlainB r := by
  intro r hr
  unfold buildArgPtrMaterialize at hr
  obtain ⟨⟨abiReg, j⟩, -, hr⟩ := List.mem_flatMap.mp hr
  simp only at hr
  split at hr
  · simp at hr
  · split_ifs at hr <;>
      rcases hs : abiSlotOfExt abiReg with _ | s <;>
      simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      (try rcases hr with rfl | rfl) <;> exact plainB_of_mov rfl

theorem epilogue_plainB : ∀ r ∈ calleeSaveRestoreEpilogue ++ [⟨0, .Lret⟩], PlainB r := by
  intro r hr
  simp only [calleeSaveRestoreEpilogue, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- The site condition on a body made of a plain prefix `A`, a body `F` without its last
    instruction, and a plain tail `T`. -/
theorem fuseSiteOkB_shape {A F T : Lcmd} (hA : ∀ r ∈ A, PlainB r) (hT : ∀ r ∈ T, PlainB r)
    (hS : ScanStays slotArr F) (hSi : SiteStays slotArr F)
    (hD : ∀ r ∈ F, dstOkB slotArr r.li_i = true) (hDT : ∀ r ∈ T, dstOkB slotArr r.li_i = true) :
    fuseSiteOkB slotArr (A ++ (F.dropLast ++ T)) = true := by
  have hTs : ScanStays slotArr T := scanStays_of_idxFree fun r hr => (hT r hr).2.1
  refine fuseSiteOkB_of (SiteStays.append (SiteStays.of_noSite fun r hr => (hA r hr).1)
    (SiteStays.append hSi.dropLast (SiteStays.of_noSite fun r hr => (hT r hr).1) hTs)
    (hS.dropLast.append hTs)) ?_
  intro n i hn hsite r hr
  have hge : A.length ≤ n := by
    by_contra hlt
    rw [List.getElem?_append_left (by omega)] at hn
    rw [(hA i (List.mem_of_getElem? hn)).1] at hsite
    cases hsite
  rw [List.drop_append, List.drop_eq_nil_of_le hge, List.nil_append] at hr
  rcases List.mem_append.mp (List.mem_of_mem_drop hr) with hr | hr
  · exact hD r (List.dropLast_subset _ hr)
  · exact hDT r hr

/-- The home condition on a body made of a plain prefix `A`, a body `F` without its last
    instruction, and a plain tail `T`. -/
theorem homeOkB_shape {A F T : Lcmd} (hA : ∀ r ∈ A, PlainB r) (hT : ∀ r ∈ T, PlainB r)
    (hF : ∀ env, EnvScratch env → homeOkB slotArr env F = true) :
    homeOkB slotArr [] (A ++ (F.dropLast ++ T)) = true := by
  have he : EnvScratch [] := fun _ hp => by cases hp
  rw [homeOkB_append, homeOkB_of_noLowMul (fun r hr => (hA r hr).2.2), Bool.true_and,
    homeOkB_append, homeOkB_dropLast (hF _ (envScratch_foldl he A)), Bool.true_and]
  exact homeOkB_of_noLowMul (fun r hr => (hT r hr).2.2) _

/-- **The expansions of the export keep the side conditions.** For a call-free allocator
    input `body1` whose accesses have reloaded bases (`hshape`), whose array operands name no
    array slot (`harr`), whose instructions other than accesses have no register-indexed
    operand (`hidx`), with array slots of prefix `qsave.` (`hslot`), the flat map of the
    expansions without their `LIVEPIN` instructions keeps its scans and those of every suffix
    behind a site, satisfies `homeOkB` from every environment that records only reload
    scratches, and writes no array slot. -/
theorem physExpand_flatMap_side {slotArr : String → Option (String × Nat)}
    (shiftImm : ShiftImmOracle) (body1 : Lcmd) (mbr : String → Option String)
    (hcf : bodyHasCall body1 = false)
    (hshape : ∀ i ∈ body1, AccForm slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o)
      mbr i.li_i)
    (harr : ∀ i ∈ body1, ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → slotArr q = none)
    (hidx : ∀ i ∈ body1, isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true)
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    let F := body1.flatMap fun i => (physExpand shiftImm (LprogAsmPrinter.bodyIsU64 body1)
      (physRmap body1 []) mbr i).filter notLivePin
    ScanStays slotArr F ∧ SiteStays slotArr F ∧
      (∀ env, EnvScratch env → homeOkB slotArr env F = true) ∧
      ∀ r ∈ F, dstOkB slotArr r.li_i = true := by
  intro F
  let rm := fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o
  have hrmE : physRmap body1 [] = rm := by
    simp only [physRmap, hcf, Bool.false_eq_true, if_false]
    rfl
  have hcall : ∀ i ∈ body1, ∀ a b, i.li_i ≠ .Lcall a b := by
    intro i hi a b he
    have := List.any_eq_false.mp hcf i hi
    rw [he] at this
    exact this rfl
  have hs15 : slotArr reloadScratch = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hs14 : slotArr reloadScratch2 = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hmem : ∀ c, slotArr ("mem." ++ c) = none := fun c =>
    slotArr_none_of_prefix hslot (hasPrefix_qsave_mem c)
  have hP : ∀ p, slotArr (physRegName p x86Abi) = none := fun p =>
    slotArr_none_of_prefix hslot (hasPrefix_qsave_physRegName p)
  have hok : ∀ i ∈ body1, ∀ x ∈ lopnOperands i.li_i, OperandOk slotArr (rm x) := by
    intro i hi x hx
    cases x with
    | reg n => exact ⟨fun q hq => by cases hq; exact hP _, nofun, nofun⟩
    | arrIdx b y s => exact ⟨nofun, nofun, fun q j sc hq => by cases hq; exact hP _⟩
    | arr q n => exact ⟨nofun, fun q' n' hq => by cases hq; exact harr i hi q n hx, nofun⟩
    | imm _ => exact ⟨nofun, nofun, nofun⟩
  have hblk : ∀ i ∈ body1, BlockOk slotArr i.li_i (physExpand shiftImm
      (LprogAsmPrinter.bodyIsU64 body1) rm mbr i) := by
    intro i hi
    rw [← hrmE, ← physPositionEmit_eq_physExpand shiftImm body1 reloadScratch2 reloadScratch2 0
      mbr [] [] i 0 (hcall i hi)]
    exact physPositionEmit_physImg shiftImm body1 reloadScratch2 reloadScratch2 0 mbr [] [] i 0
      rm (by simp [hcf, rm]) (hcall i hi) hs15 hs14 hmem (hok i hi) (fun n => ⟨_, rfl⟩)
      (hshape i hi)
  have hrmR : ∀ x n, rm x = .reg n → n ∉ fuseReloadScratches ∧ slotArr n = none := by
    intro x n h
    cases x with
    | reg m =>
      simp only [rm, remapOperand, LOperand.reg.injEq] at h
      subst h
      exact ⟨physRegName_not_scratch _, hP _⟩
    | _ => simp [rm, remapOperand] at h
  have hside := fun i (hi : i ∈ body1) => physExpand_block hs15 shiftImm
    (LprogAsmPrinter.bodyIsU64 body1) rm mbr i
    (fun r hr ds o ss he => ((hblk i hi).1 r hr ds o ss he).2)
    (fun x hx => noIdxB_remapOperand _ _ hx) hrmR (fun n => ⟨_, rfl⟩) (hshape i hi)
    (hidx i hi)
  simp only [F, hrmE]
  obtain ⟨h1, h2⟩ := SiteStays.flatMap (slotArr := slotArr) fun i hi =>
    ⟨(hside i hi).2.1, (hside i hi).1⟩
  refine ⟨h2, h1, homeOkB_flatMap fun i hi => (hside i hi).2.2, fun r hr => ?_⟩
  obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
  exact dstOkB_of_dstOk fun ds o ss he =>
    ((hblk i hi).1 r (List.mem_of_mem_filter hr) ds o ss he).1

/-- **The site condition of the fusion holds of the call-free looped physical ABI export**,
    under the hypotheses of `physImgB_lfundefPhysAbiOfVirtCert` and `hidx`: the instructions
    of the allocator input other than its accesses have no register-indexed operand. -/
theorem fuseSiteOkB_lfundefPhysAbiOfVirtCert {slotArr : String → Option (String × Nat)}
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
        match abiSaveOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false)
    (hshape : ∀ i ∈ body1, AccForm slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o)
      mbr i.li_i)
    (harr : ∀ i ∈ body1, ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → slotArr q = none)
    (hidx : ∀ i ∈ body1, isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true)
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    fuseSiteOkB slotArr (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body = true := by
  rw [lfundefPhysAbiOfVirtCert_body virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin
    posBind body1 hb1 mbr hmbr hcf, List.filter_flatMap]
  obtain ⟨hS, hSi, -, hD⟩ := physExpand_flatMap_side (certShiftImm shiftImm body1) body1 mbr hcf
    hshape harr hidx hslot
  unfold insertEpilogue
  rw [← List.append_assoc, List.append_assoc _ calleeSaveRestoreEpilogue]
  refine fuseSiteOkB_shape (fun r hr => ?_) epilogue_plainB hS hSi hD (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · exact prologue_plainB _ _ _ r hr
    · exact buildArgPtrMaterialize_plainB _ _ _ _ r hr
  · rcases List.mem_append.mp hr with hr | hr
    · exact dstOkB_of_dstOk (calleeSaveRestoreEpilogue_dstOk hslot r hr)
    · simp only [List.mem_singleton] at hr; subst hr; rfl

/-- **The home condition of the fusion holds of the call-free looped physical ABI export**,
    under the hypotheses of `fuseSiteOkB_lfundefPhysAbiOfVirtCert`. -/
theorem homeOkB_lfundefPhysAbiOfVirtCert {slotArr : String → Option (String × Nat)}
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
        match abiSaveOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false)
    (hshape : ∀ i ∈ body1, AccForm slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o)
      mbr i.li_i)
    (harr : ∀ i ∈ body1, ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → slotArr q = none)
    (hidx : ∀ i ∈ body1, isAccB i.li_i = false → ∀ x ∈ lopnOperands i.li_i, noIdxB x = true)
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    homeOkB slotArr [] (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body = true := by
  rw [lfundefPhysAbiOfVirtCert_body virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin
    posBind body1 hb1 mbr hmbr hcf, List.filter_flatMap]
  obtain ⟨-, -, hH, -⟩ := physExpand_flatMap_side (certShiftImm shiftImm body1) body1 mbr hcf
    hshape harr hidx hslot
  unfold insertEpilogue
  rw [← List.append_assoc, List.append_assoc _ calleeSaveRestoreEpilogue]
  refine homeOkB_shape (fun r hr => ?_) epilogue_plainB hH
  rcases List.mem_append.mp hr with hr | hr
  · exact prologue_plainB _ _ _ r hr
  · exact buildArgPtrMaterialize_plainB _ _ _ _ r hr

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc
