/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgSide
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgFlag

/-!
# No indexed access while a compare is open in the allocated function of the region route

Conjunct 8 of the side conditions `physImgSideB` of the printer takes `cmpScratchFreeB` on the
two-address legalisation of the re-allocated body. `PhysImgSideCmp.cmpScratchFreeB_twoAddrBody`
derives it from `cmpAccFreeB false` on the allocated body: no indexed access follows a compare
with only operations between them. This module proves `cmpAccFreeB false` on the body of the
allocated function `RegionPhysImgGate.regionAllocFn`.

The compares of the region export `exportR` are the loop guards and the zero-trip guards
`CMP:64 c, [c, #0]`, each followed by its conditional jump; every other instruction of the
export is no compare. The export is therefore closed (`CmpClosed`): it passes `cmpAccFreeB`
from the closed state and leaves no compare open. The renaming of the array positions, the
removal of self moves, the liveness instructions `LIVEPIN`, `canonicalizeMemrefThread` and
the return refine the code for `cmpAccFreeB` (`PhysImgSideCmp.CmpRefines`), and so does the
dead-write elimination `deadWriteRet`, which removes operations only.

## Main results

* `isCmpB_lopn`: a compare has the mnemonic `CMP`, `CMP:64` or `CMP^t`.
* `exportR_cmpClosed`: the region export is closed for `cmpAccFreeB`.
* `cmpRefines_regionAllocCode`: the allocator input code refines the exported code.
* `cmpAccFreeB_regionAllocBody`: `cmpAccFreeB false` on the allocator input body.
* `cmpAccFreeB_regionAllocFn`: `cmpAccFreeB false` on the body of `regionAllocFn`.
* `cmpRefines_deadWriteRet`: the dead-write elimination refines the body.
* `cmpScratchFreeB_regionAllocFn`: the compare-scratch conjunct of `physImgSideB` on the body
  of `regionAllocFn`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgCmp

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data tieBase twoAddrBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit (isAccB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint (cmpScratchFreeB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideCmp (isCmpB isOpnB isMemB cmpOpenStep
  cmpOpenAfter cmpAccFreeB CmpRefines QuietI cmpAccFreeB_append cmpOpenAfter_append
  cmpAccFreeB_of_noAcc opsNoCmp_eval cmpRefines_flatMap cmpRefines_map cmpRefines_ops
  cmpAccFreeB_quiet_left cmpAccFreeB_quiet_right cmpAccFreeB_lfundefPhysAbiOfVirtCert
  cmpScratchFreeB_twoAddrBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open RegionPhysImgGate
open RegionPhysImgFlag (FlagForm bindOps_flagForm)
open RegionPhysImgArg (renArr_lopn)
open RegionAllocMapAlign (regionAllocBody)

/-! ## 1. Compares -/

/-- A list containing `^` keeps, after its prefix without `^`, a tail starting with `^`. -/
theorem dropWhile_ne_caret {l : List Char} (h : l.contains '^' = true) :
    ∃ t, l.dropWhile (fun c => c != '^') = '^' :: t := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : a = '^'
    · subst ha
      exact ⟨l, by simp⟩
    · simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h
      simp only [List.dropWhile_cons, bne_iff_ne, ne_eq, ha, not_false_eq_true, ↓reduceIte]
      exact ih (h.resolve_left fun e => ha e.symm)

/-- **A compare has the mnemonic `CMP`, `CMP:64` or `CMP^t`.** -/
theorem isCmpB_lopn {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : isCmpB (.Lopn ds o ss) = true) :
    o = "CMP" ∨ o = "CMP:64" ∨ ∃ t, o.toList = 'C' :: 'M' :: 'P' :: '^' :: t := by
  simp only [isCmpB, stripWidthTag, beq_iff_eq] at h
  split_ifs at h with hc hs
  · right; right
    have hsplit := List.takeWhile_append_dropWhile (p := fun c => c != '^') (l := o.toList)
    have htw : o.toList.takeWhile (fun c => c != '^') = ['C', 'M', 'P'] := by
      have := congrArg String.toList h
      rw [String.toList_ofList] at this
      exact this
    obtain ⟨t, ht⟩ := dropWhile_ne_caret hc
    refine ⟨t, ?_⟩
    rw [← hsplit, htw, ht]
    rfl
  · right; left
    unfold hasSuffix at hs
    obtain ⟨t, ht⟩ := List.isSuffixOf_iff_suffix.mp hs
    have hd : o.toList.dropLast.dropLast.dropLast = t := by
      rw [← ht]
      simp
    rw [hd] at h
    have ht' : t = "CMP".toList := by rw [← h, String.toList_ofList]
    apply String.toList_inj.mp
    rw [← ht, ht']
    rfl
  · left; exact h

/-- An instruction of the flag form whose mnemonic is not the 64-bit `CMP` is no compare. -/
theorem isCmpB_of_flagForm {w : LinstrR} (hf : FlagForm w)
    (hm : ∀ ds o ss, w = .Lopn ds o ss → o ≠ "CMP:64") : isCmpB w = false := by
  cases hw : w with
  | Lopn ds o ss =>
    cases hc : isCmpB (.Lopn ds o ss)
    · rfl
    · exfalso
      have hfl : x86Data.flagOnly (tieBase o) = true := by
        rcases isCmpB_lopn hc with rfl | rfl | ⟨t, ht⟩
        · decide
        · decide
        · simp [tieBase, ht]
      exact hm ds o ss hw (hf ds o ss hw hfl).1
  | _ => rfl

theorem isCmpB_mn {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : (stripWidthTag o == "CMP") = false) : isCmpB (.Lopn ds o ss) = false := h

theorem isMemB_mn {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : (X86Backend.LprogAsmPrinter.untagCaret o == "LOADIDX"
      || X86Backend.LprogAsmPrinter.untagCaret o == "STOREIDX"
      || (X86Backend.LprogAsmPrinter.untagCaret o == "ZEROARR"
        || X86Backend.LprogAsmPrinter.untagCaret o == "STOREIMM")) = false) :
    isMemB (.Lopn ds o ss) = false := h

/-- Every instruction of a typed code is no compare. -/
def NoCmp (L : List LinstrRM) : Prop := ∀ x ∈ L, isCmpB x.1 = false

@[simp] theorem noCmp_nil : NoCmp [] := by simp [NoCmp]

@[simp] theorem noCmp_append (a b : List LinstrRM) : NoCmp (a ++ b) ↔ NoCmp a ∧ NoCmp b := by
  simp only [NoCmp, List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

@[simp] theorem noCmp_cons (x : LinstrRM) (l : List LinstrRM) :
    NoCmp (x :: l) ↔ isCmpB x.1 = false ∧ NoCmp l := by
  simp [NoCmp]

@[simp] theorem isCmpB_movI (dst : String) (src : LOperand) : isCmpB (movI dst src).1 = false :=
  isCmpB_mn (by decide +kernel)

@[simp] theorem isCmpB_movImmI (dst : String) (k : Nat) : isCmpB (movImmI dst k).1 = false :=
  isCmpB_movI _ _

@[simp] theorem isCmpB_labelI (l : LLabel) : isCmpB (labelI l).1 = false := rfl

theorem noCmp_map_movI {α : Type} (l : List α) (f : α → String) (g : α → LOperand) :
    NoCmp (l.map fun p => movI (f p) (g p)) := by
  intro x hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
  exact isCmpB_movI _ _

@[simp] theorem noCmp_stageMoves (D : Nat) (ops : List LOperand) : NoCmp (stageMoves D ops) :=
  noCmp_map_movI _ _ _

@[simp] theorem noCmp_commitMoves (D : Nat) (tgts : List String) :
    NoCmp (commitMoves D tgts) := noCmp_map_movI _ _ _

@[simp] theorem noCmp_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) :
    NoCmp (ExportRegions.parMoves D tgts ops) := by
  simp [ExportRegions.parMoves]

@[simp] theorem noCmp_seedMoves (car : List String) (ops : List LOperand) :
    NoCmp (seedMoves car ops) := noCmp_map_movI _ _ _

@[simp] theorem noCmp_shiftMoves (d nCar : Nat) : NoCmp (shiftMoves d nCar) :=
  noCmp_map_movI _ _ _

@[simp] theorem noCmp_advanceOps (idx ctr : String) : NoCmp (advanceOps idx ctr) := by
  simp only [advanceOps, noCmp_cons, noCmp_nil, and_true]
  exact ⟨isCmpB_mn (by decide +kernel), isCmpB_mn (by decide +kernel)⟩

@[simp] theorem noCmp_arrMoves (z t : String) (mv : List ArrMove) : NoCmp (arrMoves z t mv) := by
  intro x hx
  obtain ⟨a, -, hx⟩ := List.mem_flatMap.mp hx
  simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact isCmpB_mn (by decide +kernel)

@[simp] theorem noCmp_typedMoves (z t : String) (tp : List (JasminTy × String × String)) :
    NoCmp (typedMoves z t tp) := by
  simp [typedMoves, regMoves, noCmp_map_movI]

@[simp] theorem noCmp_arrParMoves (z t : String) (D : Nat) (mv : List ArrMove) :
    NoCmp (arrParMoves z t D mv) := by
  unfold arrParMoves; split <;> simp

@[simp] theorem noCmp_ifResMoves (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    NoCmp (ifResMoves rs d D ops) := by
  unfold ifResMoves; split <;> simp

@[simp] theorem noCmp_flagWord (r z : String) (op : LOperand) :
    NoCmp (flagWord x86Data r z op) := by
  unfold flagWord
  split
  · rw [show x86Data.selectMnemonic = some "CMOV" from rfl]
    simp only [noCmp_cons, noCmp_nil, isCmpB_movImmI, true_and, and_true]
    exact isCmpB_mn (by decide +kernel)
  · simp

/-- **No instruction of the binding of a program of the stack-memory fragment is a
    compare.** -/
theorem noCmp_bindOps (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (hop : opMemB e.op = true) (d : Nat) :
    NoCmp (bindOps nArgs e d) := by
  have hm : ∀ i ∈ bindOps nArgs e d, ∀ ds o ss, i.1 = .Lopn ds o ss → o ≠ "CMP:64" := by
    have hO : ∀ (dst : String) (srcs : List LOperand) ds o ss,
        opToLinstrR e.op dst srcs = .Lopn ds o ss → o ≠ "CMP:64" := by
      intro dst srcs ds o ss he
      obtain ⟨ds', o', ss', he', ho⟩ := RegionAllocMapDom.mnemOK_opToLinstrR hop dst srcs
      rw [he'] at he
      simp only [LinstrR.Lopn.injEq] at he
      obtain ⟨-, rfl, -⟩ := he
      exact ho.2.1
    intro i hi
    simp only [bindOps, JasminLsemMem.straightOpsMem, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    subst hi
    split <;> try exact hO _ _
    split
    all_goals first
      | exact hO _ _
      | (intro ds o ss he
         simp only [JasminLsemShift.shiftLinstr, LinstrR.Lopn.injEq] at he
         obtain ⟨-, rfl, -⟩ := he
         intro e
         have hb := congrArg tieBase e
         rw [AllocForm.tieBase_withWidthTag _ (by decide)] at hb
         exact absurd hb (by decide))
  intro i hi
  exact isCmpB_of_flagForm (bindOps_flagForm nArgs e d i hi) (hm i hi)

/-! ## 2. Closed codes -/

/-- The instruction of a typed instruction, at the source position `0`. -/
def toL (i : LinstrRM) : Linstr := ⟨0, i.1⟩

/-- **A closed code**: from the closed state the code passes `cmpAccFreeB` and leaves no
    compare open. -/
def CmpClosed (L : List LinstrRM) : Prop :=
  cmpAccFreeB false (L.map toL) = true ∧ cmpOpenAfter false (L.map toL) = false

theorem cmpClosed_nil : CmpClosed [] := ⟨rfl, rfl⟩

theorem cmpClosed_append {a b : List LinstrRM} (ha : CmpClosed a) (hb : CmpClosed b) :
    CmpClosed (a ++ b) := by
  refine ⟨?_, ?_⟩
  · rw [List.map_append, cmpAccFreeB_append, ha.1, ha.2, hb.1]; rfl
  · rw [List.map_append, cmpOpenAfter_append, ha.2, hb.2]

theorem cmpClosed_cons {x : LinstrRM} {l : List LinstrRM} (hx : isCmpB x.1 = false)
    (hl : CmpClosed l) : CmpClosed (x :: l) := by
  have h1 : CmpClosed [x] := by
    refine ⟨?_, ?_⟩
    · simp [cmpAccFreeB, toL]
    · simp [cmpOpenAfter, cmpOpenStep, toL, hx]
  exact cmpClosed_append h1 hl

/-- A compare followed by an instruction other than an operation closes. -/
theorem cmpClosed_cons_ctl {x y : LinstrRM} {l : List LinstrRM} (hy : isOpnB y.1 = false)
    (hl : CmpClosed l) : CmpClosed (x :: y :: l) := by
  have hya : isMemB y.1 = false := by
    cases hw : y.1 <;> rw [hw] at hy <;> first | rfl | cases hy
  have h1 : CmpClosed [x, y] := by
    refine ⟨?_, ?_⟩
    · simp [cmpAccFreeB, toL, hya]
    · simp [cmpOpenAfter, cmpOpenStep, toL, hy]
  exact cmpClosed_append (a := [x, y]) h1 hl

theorem cmpClosed_noCmp_append {a b : List LinstrRM} (ha : NoCmp a) (hb : CmpClosed b) :
    CmpClosed (a ++ b) := by
  induction a with
  | nil => exact hb
  | cons x a ih =>
    rw [noCmp_cons] at ha
    exact cmpClosed_cons ha.1 (ih ha.2)

theorem cmpClosed_of_noCmp {a : List LinstrRM} (ha : NoCmp a) : CmpClosed a := by
  simpa using cmpClosed_noCmp_append ha cmpClosed_nil

theorem cmpClosed_loopGuard_append (c : String) (t : LLabel) {l : List LinstrRM}
    (hl : CmpClosed l) : CmpClosed ((x86Data.loopGuard c t).map guardI ++ l) := by
  rw [X86Backend.TwoAddrLegalize.x86Data_loopGuard]
  exact cmpClosed_cons_ctl rfl hl

theorem cmpClosed_zeroTripGuard_append (c : String) (t e : LLabel) {l : List LinstrRM}
    (hl : CmpClosed l) : CmpClosed ((x86Data.zeroTripGuard c t e).map guardI ++ l) := by
  rw [X86Backend.TwoAddrLegalize.x86Data_zeroTripGuard]
  exact cmpClosed_cons_ctl rfl hl

/-! ## 3. The export -/

theorem forArrFrame_cmpClosed (d n : Nat) (cs : List JasminTy) (initOps : List LOperand)
    (countOp : LOperand) (bodyC : List LinstrRM) (bodyOps : List LOperand) (bodyD : Nat)
    (hb : CmpClosed bodyC) :
    CmpClosed (forArrFrame d n cs initOps countOp bodyC bodyOps bodyD x86Data) := by
  unfold forArrFrame
  refine cmpClosed_cons (isCmpB_movImmI _ _) (cmpClosed_noCmp_append (noCmp_typedMoves _ _ _) ?_)
  refine cmpClosed_noCmp_append (noCmp_seedMoves _ _) (cmpClosed_zeroTripGuard_append _ _ _ ?_)
  refine cmpClosed_cons rfl (cmpClosed_append hb (cmpClosed_cons (isCmpB_movImmI _ _) ?_))
  refine cmpClosed_noCmp_append (noCmp_arrParMoves _ _ _ _) ?_
  refine cmpClosed_noCmp_append (noCmp_parMoves _ _ _) ?_
  refine cmpClosed_noCmp_append (noCmp_advanceOps _ _) (cmpClosed_loopGuard_append _ _ ?_)
  exact cmpClosed_cons rfl (cmpClosed_cons (isCmpB_movImmI _ _)
    (cmpClosed_of_noCmp (noCmp_typedMoves _ _ _)))

theorem whileFrame_cmpClosed (d n nCar : Nat) (initOps : List LOperand)
    (bodyC : List LinstrRM) (flagOp : LOperand) (bodyOps : List LOperand) (bodyD : Nat)
    (hb : CmpClosed bodyC) :
    CmpClosed (whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD x86Data) := by
  unfold whileFrame
  have hg := cmpClosed_loopGuard_append (regName (bodyD + nCar)) n cmpClosed_nil
  rw [List.append_nil] at hg
  exact cmpClosed_noCmp_append (noCmp_seedMoves _ _) (cmpClosed_cons rfl (cmpClosed_append hb
    (cmpClosed_noCmp_append (noCmp_flagWord _ _ _) (cmpClosed_noCmp_append
      (noCmp_parMoves _ _ _) hg))))

theorem ifFrame_cmpClosed (fn : String) (d n : Nat) (rs : List JasminTy) (condOp : LOperand)
    (thnC : List LinstrRM) (thnOps : List LOperand) (thnD : Nat)
    (elsC : List LinstrRM) (elsOps : List LOperand) (elsD : Nat)
    (ht : CmpClosed thnC) (he : CmpClosed elsC) :
    CmpClosed (ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD x86Data) := by
  unfold ifFrame
  exact cmpClosed_noCmp_append (noCmp_flagWord _ _ _) (cmpClosed_zeroTripGuard_append _ _ _
    (cmpClosed_cons rfl (cmpClosed_append ht (cmpClosed_noCmp_append (noCmp_ifResMoves _ _ _ _)
      (cmpClosed_cons (isCmpB_movImmI _ _) (cmpClosed_loopGuard_append _ _ (cmpClosed_cons rfl
        (cmpClosed_append he (cmpClosed_noCmp_append (noCmp_ifResMoves _ _ _ _)
          (cmpClosed_cons rfl cmpClosed_nil))))))))))

/-- **The region export is closed for `cmpAccFreeB`**: for a program without `call` that
    passes `regionExportableB`, the export on x86 passes `cmpAccFreeB` from the closed state
    and leaves no compare open. Its compares are the loop and zero-trip guards, each followed
    by its conditional jump. -/
theorem exportR_cmpClosed (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r →
      CmpClosed r.code := by
  induction p with
  | ret vs =>
    intro d n r h
    simp only [exportR, Option.some.injEq] at h
    subst h; exact cmpClosed_nil
  | var e k ih =>
    simp only [regionExportableB, Bool.and_eq_true] at hp
    simp only [NFProg.callFree] at hc
    intro d n r h
    simp only [exportR, Option.map_eq_some_iff] at h
    obtain ⟨rk, hk, rfl⟩ := h
    exact cmpClosed_noCmp_append (noCmp_bindOps nArgs e hp.1 d) (ih hp.2 hc _ _ _ hk)
  | forLoop count inits body k ihb ihk =>
    simp only [regionExportableB, Bool.and_eq_true] at hp
    simp only [NFProg.callFree, Bool.and_eq_true] at hc
    intro d n r h
    simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rk, hk, rfl⟩ := h
    exact cmpClosed_append (forArrFrame_cmpClosed _ _ _ _ _ _ _ _ (ihb hp.1 hc.1 _ _ _ hb))
      (ihk hp.2 hc.2 _ _ _ hk)
  | ifThenElse cond thn els k iht ihe ihk =>
    simp only [regionExportableB, Bool.and_eq_true] at hp
    simp only [NFProg.callFree, Bool.and_eq_true] at hc
    intro d n r h
    simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
    exact cmpClosed_append (ifFrame_cmpClosed _ _ _ _ _ _ _ _ _ _ _
      (iht hp.1.1 hc.1.1 _ _ _ ht) (ihe hp.1.2 hc.1.2 _ _ _ he)) (ihk hp.2 hc.2 _ _ _ hk)
  | whileLoop inits body k ihb ihk =>
    simp only [regionExportableB, Bool.and_eq_true] at hp
    simp only [NFProg.callFree, Bool.and_eq_true] at hc
    intro d n r h
    simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rk, hk, rfl⟩ := h
    exact cmpClosed_append (whileFrame_cmpClosed _ _ _ _ _ _ _ _ (ihb hp.1.2 hc.1 _ _ _ hb))
      (ihk hp.2 hc.2 _ _ _ hk)
  | call f args k ih =>
    simp [NFProg.callFree] at hc

theorem noCmp_regionLprogCopy (a : AbiNames) (ts : List JasminTy) (code : List LinstrRM)
    (res : List LOperand) : NoCmp (regionLprogCopy a none ts code res) := by
  intro i hi
  unfold regionLprogCopy at hi
  split at hi
  · split at hi
    · obtain ⟨j, -, hi⟩ := List.mem_flatMap.mp hi
      simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact isCmpB_movImmI _ _
      · exact isCmpB_mn (by decide +kernel)
      · exact isCmpB_mn (by decide +kernel)
    · cases hi
  · cases hi

/-! ## 4. The allocator input -/

/-- One instruction refines another when it is an operation only under a mnemonic of the
    other, which is then an operation. -/
theorem cmpRefines_one_of_mn {i j : Linstr}
    (h : ∀ ds o ss, j.li_i = .Lopn ds o ss → ∃ ds' ss', i.li_i = .Lopn ds' o ss') :
    CmpRefines [j] [i] := by
  cases hj : j.li_i with
  | Lopn ds o ss =>
    obtain ⟨ds', ss', hi⟩ := h ds o ss hj
    refine cmpRefines_ops (by rw [hi]; rfl) (fun r hr ha => ?_) (fun r hr hc => ?_)
    · rw [List.mem_singleton] at hr; subst hr; rw [hj] at ha; rw [hi]; exact ha
    · rw [List.mem_singleton] at hr; subst hr; rw [hj] at hc; rw [hi]; exact hc
  | _ =>
    intro w hA
    refine ⟨?_, fun _ => ?_⟩
    · simp [cmpAccFreeB, hj, isMemB, isAccB, X86Backend.PhysImgEmit.isArrImmB]
    · simp [cmpOpenAfter, cmpOpenStep, hj, isOpnB] at *

theorem cmpRefines_map_renArr (ρ : String → String) (C : List LinstrRM) :
    CmpRefines ((C.map (renArr ρ)).map toL) (C.map toL) := by
  induction C with
  | nil => exact CmpRefines.refl _
  | cons i C ih =>
    simp only [List.map_cons]
    refine (cmpRefines_one_of_mn (i := toL i) (j := toL (renArr ρ i)) fun ds o ss he => ?_).append
      ih
    obtain ⟨ds', ss', hi, -⟩ := renArr_lopn ρ he
    exact ⟨ds', ss', hi⟩

/-- Quiet operations in front of a block keep a refinement. -/
theorem cmpRefines_quietOps_left {q B A : Lcmd}
    (hq : ∀ j ∈ q, isOpnB j.li_i = true ∧ isCmpB j.li_i = false ∧ isMemB j.li_i = false)
    (h : CmpRefines B A) : CmpRefines (q ++ B) A := by
  intro w hA
  obtain ⟨hB, hB'⟩ := h w hA
  have he := opsNoCmp_eval (l := q) (fun j hj => ⟨(hq j hj).1, (hq j hj).2.1⟩) w
  refine ⟨?_, fun ho => hB' ?_⟩
  · rw [cmpAccFreeB_append, cmpAccFreeB_of_noAcc w fun j hj => (hq j hj).2.2, he.1]
    simpa using hB
  · rwa [cmpOpenAfter_append, he.1] at ho

/-- The liveness instructions in place of the self-moves keep a refinement: they are quiet
    operations, and the self-moves are operations. -/
theorem cmpRefines_pinSelfMoves : ∀ C : List LinstrRM,
    CmpRefines ((pinSelfMoves C).map toL) (C.map toL)
  | [] => CmpRefines.refl _
  | [i] => CmpRefines.refl _
  | i :: j :: rest => by
    by_cases hs : selfMoveB i j = true
    · obtain ⟨t, a, z, sc, w, n, rfl, rfl⟩ := selfMoveB_shape hs
      rw [pinSelfMoves_pair]
      simp only [List.map_cons]
      have hq : ∀ k ∈ [toL (selfPinLoad t a z), toL (selfPinStore a z t)],
          isOpnB k.li_i = true ∧ isCmpB k.li_i = false ∧ isMemB k.li_i = false := by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        all_goals exact ⟨rfl, isCmpB_mn (by decide +kernel), isMemB_mn (by decide +kernel)⟩
      exact cmpRefines_quietOps_left hq
        (((cmpRefines_pinSelfMoves rest).cons_op rfl).cons_op rfl)
    · rw [pinSelfMoves_cons (Bool.eq_false_iff.mpr hs), List.map_cons, List.map_cons]
      have := (cmpRefines_pinSelfMoves (j :: rest)).cons (toL i)
      rwa [List.map_cons] at this

theorem cmpRefines_backEdgePins (C : List LinstrRM) :
    CmpRefines ((backEdgePins C).map toL) (C.map toL) := by
  have hC : C.map toL = C.zipIdx.flatMap fun p => [toL p.1] := by
    have e : ∀ l : List (LinstrRM × Nat),
        (l.flatMap fun p => [toL p.1]) = l.map (toL ∘ Prod.fst) := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => rw [List.flatMap_cons, ih]; rfl
    rw [e, ← List.map_map, List.zipIdx_map_fst]
  rw [hC]
  unfold backEdgePins
  rw [List.map_flatMap]
  refine cmpRefines_flatMap _ fun p _ => ?_
  have hpin : ∀ T k l, ∀ j ∈ (backEdgePin T C k l).map toL,
      isOpnB j.li_i = true ∧ isCmpB j.li_i = false ∧ isMemB j.li_i = false := by
    intro T k l j hj
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hj
    unfold backEdgePin at hx
    dsimp only at hx
    split at hx
    · split at hx
      · rw [List.mem_singleton.mp hx]
        exact ⟨rfl, isCmpB_mn (by decide +kernel), isMemB_mn (by decide +kernel)⟩
      · cases hx
    · cases hx
  obtain ⟨i, k⟩ := p
  dsimp only
  split
  all_goals first
    | exact CmpRefines.refl _
    | (rw [List.map_append]
       exact cmpRefines_quietOps_left (hpin _ _ _) (CmpRefines.refl _))

/-- **The allocator input code refines the exported code** for `cmpAccFreeB`: the renaming of
    the array positions keeps every mnemonic, and the liveness instructions `LIVEPIN`, in
    place of the self moves and at the back edges, are quiet operations. -/
theorem cmpRefines_regionAllocCode (C : List LinstrRM) (outs : List (String × Nat))
    (rr : Option (String × String) := none) :
    CmpRefines ((regionAllocCode C outs rr).map toL) (C.map toL) :=
  (cmpRefines_backEdgePins _).trans ((cmpRefines_pinSelfMoves _).trans
    (cmpRefines_map_renArr _ C))

theorem cmpRefines_canonicalizeMemrefThread (body : Lcmd) :
    CmpRefines (canonicalizeMemrefThread body) body := by
  unfold canonicalizeMemrefThread
  dsimp only
  split
  · exact CmpRefines.refl _
  · refine cmpRefines_map _ body fun i _ => cmpRefines_one_of_mn fun ds o ss he => ?_
    split at he
    · next ds0 o0 ss0 heq =>
      simp only [LinstrR.Lopn.injEq] at he
      obtain ⟨-, rfl, -⟩ := he
      exact ⟨ds0, ss0, heq⟩
    · exact ⟨ds, ss, he⟩

theorem quietI_livepin (ii : Nat) (ss : List LOperand) :
    QuietI ⟨ii, .Lopn [.reg "%livepin"] "LIVEPIN" ss⟩ :=
  ⟨isCmpB_mn (by decide +kernel), isMemB_mn (by decide +kernel)⟩

/-- **`cmpAccFreeB` on the allocator input body**: for a program without `call` that passes
    `regionExportableB`, the body `regionAllocBody` of a result other than one register
    passes `cmpAccFreeB` from the closed state. -/
theorem cmpAccFreeB_regionAllocBody (fn : String) (a : AbiNames) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 x86Data = some r) (hts : ∀ w, ts ≠ [.reg w]) :
    cmpAccFreeB false (regionAllocBody a Γ.length ts r) = true := by
  have hC : CmpClosed (r.code ++ regionLprogCopy a none ts r.code r.res) :=
    cmpClosed_append (exportR_cmpClosed _ _ p hp hc _ _ r hr)
      (cmpClosed_of_noCmp (noCmp_regionLprogCopy a ts _ _))
  have hac := (cmpRefines_regionAllocCode
    (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res)).final hC.1
  have hbody : cmpAccFreeB false
      (arrBasePins a (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res))
        ++ ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res)).map
          (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩])) = true := by
    refine cmpAccFreeB_quiet_left (fun j hj => ?_)
      (cmpAccFreeB_quiet_right hac fun j hj => ?_)
    · unfold arrBasePins at hj
      dsimp only at hj
      split at hj
      · cases hj
      · rw [List.mem_singleton.mp hj]; exact quietI_livepin _ _
    · rw [List.mem_singleton.mp hj]; exact ⟨rfl, rfl⟩
  unfold regionAllocBody
  split
  · exact absurd rfl (hts _)
  · refine cmpAccFreeB_quiet_left (fun j hj => ?_)
      ((cmpRefines_canonicalizeMemrefThread _).final hbody)
    split at hj
    · rw [List.mem_singleton.mp hj]; exact quietI_livepin _ _
    · cases hj

/-! ## 5. The allocated function -/

/-- **`cmpAccFreeB` on the allocated function of the region route**: for a program without
    `call` that passes `regionExportableB`, with a result other than one register, no indexed
    access of the body of `regionAllocFn` follows a compare with only operations between
    them. -/
theorem cmpAccFreeB_regionAllocFn (fn : String) (a : AbiNames) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 x86Data = some r) (hts : ∀ w, ts ≠ [.reg w])
    (fd0 : Lfundef) : cmpAccFreeB false (regionAllocFn a ts r fd0).lfd_body = true := by
  have hB : ∀ i ∈ regionAllocBody a Γ.length ts r, RegionAllocMapDom.ShapeB i.li_i :=
    RegionAllocMapDom.shapeB_regionAllocBody _ _ ts r fun i hi =>
      (RegionAllocMapDom.exportR_mnemDom Γ.length fn p hp hc _ _ r hr i hi).2.2
  have hcf := RegionAllocMapDom.bodyHasCall_of_shapeB hB
  have hb1 : regionAllocBody a Γ.length ts r =
      (if a.abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range a.abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (([] : List String).foldl (fun b r => aliasRegBody r a.outArg b)
            (arrBasePins a (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res))
              ++ ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res)).map
                (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]))) := by
    unfold regionAllocBody
    split
    · exact absurd rfl (hts _)
    · rfl
  unfold regionAllocFn calleeAllocCert
  exact cmpAccFreeB_lfundefPhysAbiOfVirtCert _ _ _ [] (fun _ => none) _ _ true _ hb1 _ rfl hcf
    (cmpAccFreeB_regionAllocBody fn a p hp hc hr hts)

/-! ## 6. The dead-write elimination -/

theorem cmpRefines_dropDeadWriteBody : ∀ l : Lcmd,
    CmpRefines (X86Backend.OwnedLprogTV.dropDeadWriteBody l) l
  | [] => CmpRefines.refl _
  | i :: l => by
    have ih := cmpRefines_dropDeadWriteBody l
    unfold X86Backend.OwnedLprogTV.dropDeadWriteBody at ih ⊢
    simp only [X86Backend.OwnedLprogTV.deadWriteMarks]
    cases hd : X86Backend.OwnedLprogTV.pureWrDst? i.li_i with
    | none =>
      simp only [X86Backend.OwnedLprogTV.keptL, List.filter_cons, Bool.not_false,
        ite_true, List.map_cons] at ih ⊢
      exact ih.cons i
    | some d =>
      have hop : isOpnB i.li_i = true := by
        unfold X86Backend.OwnedLprogTV.pureWrDst? at hd
        split at hd
        · next heq => rw [heq]; rfl
        · cases hd
      cases hm : (X86Backend.OwnedLprogTV.straightR i.li_i &&
          X86Backend.OwnedLprogTV.killedByMulx d (X86Backend.OwnedLprogTV.deadWriteMarks l))
      · simp only [X86Backend.OwnedLprogTV.keptL, List.filter_cons, hm, Bool.not_false,
          ite_true, List.map_cons] at ih ⊢
        exact ih.cons i
      · simp only [X86Backend.OwnedLprogTV.keptL, List.filter_cons, hm, Bool.not_true,
          Bool.false_eq_true, ite_false] at ih ⊢
        exact ih.cons_op hop

/-- **The dead-write elimination refines the body** for `cmpAccFreeB`: it removes
    operations only. -/
theorem cmpRefines_deadWriteRet (b : Lcmd) : CmpRefines (deadWriteRet b) b := by
  unfold deadWriteRet
  split
  · next r hr =>
    split
    · conv_rhs => rw [← List.dropLast_append_getLast? r hr]
      exact (cmpRefines_dropDeadWriteBody _).append (CmpRefines.refl _)
    · exact CmpRefines.refl _
  · exact CmpRefines.refl _

/-! ## 7. The compare scratch -/

/-- **Conjunct 8 of `physImgSideB` on the allocated function of the region route**: for a
    program without `call` that passes `regionExportableB`, with a result other than one
    register, at every slot map `sl` and result names `res`, the reload scan of the base of no
    indexed access of the two-address legalisation of the re-allocated body carries the reload
    scratch past a compare on a spilled first operand. -/
theorem cmpScratchFreeB_regionAllocFn (fn : String) (a : AbiNames) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 x86Data = some r) (hts : ∀ w, ts ≠ [.reg w])
    (fd0 : Lfundef) (sl : String → Option (String × Nat)) (res : List String) :
    cmpScratchFreeB sl (twoAddrBody (reallocStage res (regionAllocFn a ts r fd0).lfd_body))
      = true :=
  cmpScratchFreeB_twoAddrBody res (cmpAccFreeB_regionAllocFn fn a p hp hc hr hts fd0)
    (cmpRefines_deadWriteRet _)

/-! ## 8. The side conditions under the load-CSE conditions -/

section LoadCSE

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (splitStraightRuns)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass (memMovFreeB
  copyNoSlotB_postOpt cellBaseFreeB_postOpt flagTiedB_reallocStage cellBaseFreeB_printedChain)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgOpt (optSideB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotArrOf slotRen)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (slotArrC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiBody)
open RegionPhysImgSide (sideAlloc_regionAllocFn deadWriteRet_sublist regionAllocFn_lfd_res)

/-- **The side conditions of the region gate from the optimizer and load-CSE conditions**, on
    the domain of `RegionPhysImgArg.physImgB_regionExport_words`. For the body `b0` of
    `regionAllocFn` and its result names, at the slot map of the gate, `physImgSideB` holds
    when the optimizer condition holds on every straight run of the post-pass body (`hopt`)
    and no 64-bit move of the post-pass body is between two memory names (`hhold`). The
    site, home, cell-base, high-product and copy conditions follow from the export
    (`RegionPhysImgSide.sideAlloc_regionAllocFn`), the tied compares from
    `RegionPhysImgFlag.flagTiedB_regionAllocFn` and the compare scratch from
    `cmpScratchFreeB_regionAllocFn`. -/
theorem physImgSideB_of_loadCSE (fname : String) (σ : AbiLayout) {ts : List JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hw : RegionPhysImgArg.arrW64B p = true)
    (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    {r : Exported} (hr : exportR (nfCtx σ).length fname p (nfCtx σ).length 0 = some r)
    (hzr : RegionPhysImgArg.ZeroAtRoot (nfAbiNames fname σ) ts r)
    (hts : ∀ w, ts ≠ [.reg w]) (fd0 : Lfundef)
    (hnd : (σ.args.map fun a => exportReg a.reg).Nodup) (R : Slots)
    (ps : List (String × String))
    (hopt : (splitStraightRuns
      (postBody (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body)).all
      (optSideB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))) = true)
    (hhold : memMovFreeB (postBody (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body)
      = true) :
    physImgSideB (slotArrC R (slotRen (slotArrOf σ exportReg) (renOf ps)))
      (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_res
      (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body = true := by
  obtain ⟨h1, h2, hcell, hmul, hcopy⟩ :=
    sideAlloc_regionAllocFn fname σ p hp hc hw hσ hr hzr hts fd0 hnd R ps
  have hq := RegionPhysImg.regionSl_qsave R σ exportReg (renOf ps)
  have hs := deadWriteRet_sublist
    (fuseMulHiBody (regionAllocFn (nfAbiNames fname σ) ts r fd0).lfd_body true)
  simp only [physImgSideB, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hopt⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact copyNoSlotB_postOpt hq hcopy hmul hs hhold
  · exact cellBaseFreeB_postOpt hcell hs
  · rw [regionAllocFn_lfd_res]; rfl
  · exact flagTiedB_reallocStage _
      (RegionPhysImgFlag.flagTiedB_regionAllocFn fname _ p hp hc hr hts fd0) hs
  · exact cmpScratchFreeB_regionAllocFn fname _ p hp hc hr hts fd0 _ _
  · exact cellBaseFreeB_printedChain _ hcell hs

/-- **The region gate never refuses at its image conjunct under the optimizer and load-CSE
    conditions**: `RegionPhysImgGate.regionCoStage_ne_physImgB` with `hside` replaced by the
    hypotheses `hopt` and `hhold` of `physImgSideB_of_loadCSE` at the slot map of the gate. -/
theorem regionCoStage_ne_physImgB_of_loadCSE (fname : String) (σ : AbiLayout) {t : JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) [t]) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hw : RegionPhysImgArg.arrW64B p = true)
    (hσ : RegionPhysImgArg.wordsSlotB σ = true)
    {r : Exported} (hr : exportR (nfCtx σ).length fname p (nfCtx σ).length 0 = some r)
    (hzr : RegionPhysImgArg.ZeroAtRoot (nfAbiNames fname σ) [t] r)
    {fd0 : Lfundef} (hfd : exportRLfundef fname p = some fd0)
    (hts : ∀ w, [t] ≠ [.reg w]) (hnd : (σ.args.map fun a => exportReg a.reg).Nodup)
    (ex : List String) (hwe : regionWebs ex r = r) {P : Lprog} {cert : List (String × String)}
    (hP : regionLprogC (nfAbiNames fname σ) p none ex = some (P, cert))
    {b : Lcmd} (hb : firstBody (printedLprog P) = some b) (fn : String)
    (hopt : (splitStraightRuns
      (postBody (regionAllocFn (nfAbiNames fname σ) [t] r fd0).lfd_body)).all
      (optSideB (slotArrC (regionCoParts σ exportReg b t r.code r.res cert).cells
        (slotRen (slotArrOf σ exportReg)
          (renOf (regionCoParts σ exportReg b t r.code r.res cert).ps)))) = true)
    (hhold : memMovFreeB (postBody (regionAllocFn (nfAbiNames fname σ) [t] r fd0).lfd_body)
      = true) :
    regionCoStage σ exportReg b t r.code r.res cert none fn ≠ some "physImgB" :=
  regionCoStage_ne_physImgB fname σ p hp hc hw hσ hr hzr hfd hts hnd ex hwe hP hb fn
    (physImgSideB_of_loadCSE fname σ p hp hc hw hσ hr hzr hts fd0 hnd _ _ hopt hhold)

end LoadCSE

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgCmp
