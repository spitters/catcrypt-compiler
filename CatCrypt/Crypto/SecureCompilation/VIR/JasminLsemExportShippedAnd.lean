/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedRen

@[expose] public section

set_option autoImplicit false

/-!
# The export loop node of the shipped `mpn_and_n_loop_owned` body on the flag machine

The LowCT front binds every `RScalarSetExpr` variable through a count-`0` left
shift, so the update `binAndUpdate` of the shipped limb body contains two
`shlImm 64 0` bindings. The model chain `straightOpsMem` emits such a binding as
the structured wire `SHL:64 dst, src, #0`; the export's body walk emits the
count-in-mnemonic wire `SHL:0:64 dst, src`. The export node renamed by a node
renaming is therefore the image of the canonicalised node `canonNodeRM` under the
immediate-shift expansion `JasminLsemExportTransfer.immShiftExpand`, and the
expansion certificate `JasminLsemExportTransfer.expProg_immShiftExpand` carries a
run of the canonicalised node to a run of its expansion.

## Main results

* `immShiftExpand_renRM` — the expansion commutes with an operand renaming.
* `ComExpOK` — every binding of a `Com` has an op in the fragment's op set, and
  every immediate shift has a count-in-mnemonic wire the decoder reads back.
* `forLoopLcmdNRtRM_map_eq_canonNodeRM_expand` — the typed export node renamed by
  `ρ` is the expansion of `canonNodeRM` at `τ = ρ ∘ σ`.
* `canonNodeRM_instrOK` — every instruction of `canonNodeRM` satisfies the
  per-instruction condition of the expansion.
* `binAndUpdate_comExpOK` — the shipped limb body satisfies `ComExpOK`.
* `binAnd_export_node_eq` — the export node of the shipped limb body, at the
  registers `MpnLoopFrontEmit.binLprog` passes, renamed by `ρ`, is the expansion
  of the canonicalised node at `ρ ∘ logicSigma d`.
* `binAnd_export_machine_shipped` — that renamed export node halts on the flag
  machine with the array at `argName 0` decoding to the source fold.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogic
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanonLogicShipped
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedRen
open CatCrypt.Crypto.SecureCompilation.VIR.LoopNameDistinct
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower (InstrOK EqPc RelX)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype (N AN)

/-! ## 1. The expansion under a renaming -/

/-- Renaming an operand keeps its constructor: an operand renames to a register
    only if it is a register. -/
theorem renOperand_eq_reg {ρ : String → String} {o : LOperand} {r : String}
    (h : renOperand ρ o = .reg r) : ∃ r', o = .reg r' := by
  cases o <;> simp_all [renOperand]

/-- An operand renames to an immediate only if it is that immediate. -/
theorem renOperand_eq_imm {ρ : String → String} {o : LOperand} {n : Nat}
    (h : renOperand ρ o = .imm n) : o = .imm n := by
  cases o <;> simp_all [renOperand]

/-- **The immediate-shift expansion commutes with an operand renaming.** -/
theorem immShiftExpand_renRM (ρ : String → String) (i : LinstrRM) :
    immShiftExpand (renRM ρ i) = (immShiftExpand i).map (renRM ρ) := by
  by_cases hs : ∃ dst opn src n,
      i = (.Lopn [.reg dst] opn [.reg src, .imm n], MemTag.reg none)
  · obtain ⟨dst, opn, src, n, rfl⟩ := hs
    show immShiftExpand (.Lopn [.reg (ρ dst)] opn [.reg (ρ src), .imm n], MemTag.reg none)
      = _
    simp only [immShiftExpand]
    split <;> rfl
  · have hi : immShiftExpand i = [i] :=
      immShiftExpand_of_not_shift i (fun a b c d h => hs ⟨a, b, c, d, h⟩)
    rw [hi, List.map_singleton]
    refine immShiftExpand_of_not_shift _ (fun dst opn src n h => hs ?_)
    obtain ⟨ins, tag⟩ := i
    cases ins with
    | Lopn ds o ss =>
        simp only [renRM, renLinstrR, Prod.mk.injEq, LinstrR.Lopn.injEq] at h
        obtain ⟨⟨hd, rfl, hsrc⟩, rfl⟩ := h
        rcases ds with _ | ⟨d1, _ | ⟨d2, drest⟩⟩
        · simp at hd
        · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hd
          obtain ⟨dst', rfl⟩ := renOperand_eq_reg hd
          rcases ss with _ | ⟨a, _ | ⟨b, _ | ⟨e, rest⟩⟩⟩
          · simp at hsrc
          · simp at hsrc
          · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsrc
            obtain ⟨ha, hb⟩ := hsrc
            obtain ⟨src', rfl⟩ := renOperand_eq_reg ha
            rw [renOperand_eq_imm hb]
            exact ⟨dst', _, src', n, rfl⟩
          · simp at hsrc
        · simp at hd
    | _ => simp [renRM, renLinstrR] at h

/-- A list whose instructions the expansion fixes is its own expansion. -/
theorem flatMap_immShiftExpand_of_fixed :
    ∀ (L : List LinstrRM), (∀ i ∈ L, immShiftExpand i = [i]) →
      L.flatMap immShiftExpand = L
  | [], _ => rfl
  | i :: is, h => by
      rw [List.flatMap_cons, h i (by simp),
        flatMap_immShiftExpand_of_fixed is (fun j hj => h j (by simp [hj]))]
      rfl

/-- The expansion of a renamed list is the renaming of the expanded list. -/
theorem map_renRM_flatMap_immShiftExpand (ρ : String → String) (L : List LinstrRM) :
    (L.flatMap immShiftExpand).map (renRM ρ) = (L.map (renRM ρ)).flatMap immShiftExpand := by
  rw [List.map_flatMap, List.flatMap_map]
  exact congrArg (List.flatMap · L) (funext fun i => (immShiftExpand_renRM ρ i).symm)

/-! ## 2. Fixed points of the expansion in the node skeleton -/

/-- The flag compare against `#0` is fixed by the expansion. -/
theorem immShiftExpand_cmp0 (r : String) :
    immShiftExpand (.Lopn [.reg r] (withWidthTag 64 "CMP") [.reg r, .imm 0], MemTag.reg none)
      = [(.Lopn [.reg r] (withWidthTag 64 "CMP") [.reg r, .imm 0], MemTag.reg none)] :=
  immShiftExpand_of_not_shiftBase _ _ _ _ (by decide)

/-- The index advance and the counter decrement are fixed by the expansion. -/
theorem loopAdvanceRM_fixed (d : Nat) : ∀ i ∈ loopAdvanceRM d, immShiftExpand i = [i] := by
  intro i hi
  simp only [loopAdvanceRM, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact immShiftExpand_of_not_shiftBase _ _ _ _ (by decide)
  · exact immShiftExpand_of_not_shiftBase _ _ _ _ (by decide)

/-- The invariant touches are fixed by the expansion. -/
theorem loopTouchRM_fixed (d : Nat) (regs : List String) :
    ∀ i ∈ loopTouchRM d regs, immShiftExpand i = [i] := by
  intro i hi
  simp only [loopTouchRM, List.mem_map] at hi
  obtain ⟨r, _, rfl⟩ := hi
  exact immShiftExpand_of_regs _ _ _ _ (by simp)

/-- The feedback move of the canonicalised body is fixed by the expansion. -/
theorem canonFeedback_fixed (out : String) (absent : Bool) :
    ∀ i ∈ canonFeedback out absent, immShiftExpand i = [i] := by
  intro i hi
  unfold canonFeedback at hi
  cases absent
  · simp only [Bool.false_eq_true, if_false, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    subst hi
    exact immShiftExpand_of_regs _ _ _ _ (by simp)
  · simp at hi

/-- The seed moves of the canonicalised node are fixed by the expansion. -/
theorem canonSeedsRM_fixed (d : Nat) (out c : String) :
    ∀ i ∈ canonSeedsRM d out c, immShiftExpand i = [i] := by
  intro i hi
  simp only [canonSeedsRM, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

/-- The guarded flag loop over an expanded body is the expansion of the guarded
    flag loop. -/
theorem guardedFlagLoopLinstrRM_flatMap (top endL : LLabel) (nReg : String)
    (body : List LinstrRM) :
    (guardedFlagLoopLinstrRM top endL nReg body).flatMap immShiftExpand
      = guardedFlagLoopLinstrRM top endL nReg (body.flatMap immShiftExpand) := by
  simp only [guardedFlagLoopLinstrRM, flagLoopLinstrRM, flagBackedge, List.flatMap_cons,
    List.flatMap_append, List.flatMap_nil, immShiftExpand_cmp0, List.cons_append,
    List.append_nil, List.nil_append, List.append_assoc]
  rfl

/-! ## 3. The export node against the expanded canonicalised node -/

/-- **The renamed looped segment is the expanded canonicalised body.** For an
    update whose ops lie in the fragment's op set, the export's looped segment
    renamed by `ρ` is the immediate-shift expansion of the canonicalised body at
    `τ = ρ ∘ σ`. -/
theorem forLoopBodyNRtRM_map_eq_canonBodyRM_expand {invTys : Ctxt jasminDialect}
    {d : Nat} {out : String} {w n : Nat} {σ ρ : String → String}
    {acc c : String} (invOps : List LOperand)
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hcom : ComOpsPlain update)
    (hσ : LoopRen σ d invTys.length acc (invRegsOf invOps))
    (hρ : NodeRen ρ d acc out c (invRegsOf invOps))
    (hret : ρ (loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
      (2 + invTys.length)).2 = out) :
    (forLoopBodyNRtRM d acc update invOps (fun _ => none)).map (renRM ρ)
      = (canonBodyRM (ρ ∘ σ) d out update
          ((loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
            (2 + invTys.length)).2 == acc) (invRegsOf invOps)).flatMap immShiftExpand := by
  have h1 : (loopBodyWalkNM d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
        (2 + invTys.length)).map (renRM ρ)
      = ((straightOpsMem (invTys.length + 2) update (invTys.length + 2)).map
          (renRM (ρ ∘ σ))).flatMap immShiftExpand := by
    rw [Nat.add_comm 2 invTys.length, loopBodyWalkNM_eq_expand hσ update hcom,
      map_renRM_flatMap_immShiftExpand, List.map_map]
    congr 1
    exact List.map_congr_left (fun i _ => renRM_comp ρ σ i)
  have h2 : ∀ ret : String, ρ ret = out →
      (loopFeedbackRM acc ret).map (renRM ρ) = canonFeedback out (ret == acc) := by
    intro ret hr
    unfold loopFeedbackRM canonFeedback
    cases hra : (ret == acc) with
    | true => simp
    | false => simp [renRM, renLinstrR, renOperand, hρ.accOut, hr]
  have h3 : (loopAdvanceRM d).map (renRM ρ) = loopAdvanceRM d := by
    simp [loopAdvanceRM, renRM, renLinstrR, renOperand, hρ.idxFix, hρ.ctrFix]
  have h4 : (loopTouchRM d (invRegsOf invOps)).map (renRM ρ)
      = loopTouchRM d (invRegsOf invOps) := by
    unfold loopTouchRM
    rw [List.map_map]
    refine List.map_congr_left (fun r hr => ?_)
    simp [renRM, renLinstrR, renOperand, hρ.ctrFix, hρ.invFix r hr]
  have htail : ∀ absent : Bool,
      (canonFeedback out absent ++ loopAdvanceRM d ++ loopTouchRM d (invRegsOf invOps)).flatMap
        immShiftExpand
        = canonFeedback out absent ++ loopAdvanceRM d ++ loopTouchRM d (invRegsOf invOps) := by
    intro absent
    refine flatMap_immShiftExpand_of_fixed _ (fun i hi => ?_)
    simp only [List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · exact canonFeedback_fixed out absent i hi
    · exact loopAdvanceRM_fixed d i hi
    · exact loopTouchRM_fixed d _ i hi
  unfold forLoopBodyNRtRM canonBodyRM
  rw [List.flatMap_append, htail]
  simp only [List.map_append, h1, h2 _ hret, h3, h4, List.append_assoc]

/-- **The renamed export node is the expanded canonicalised node.** Under the
    hypotheses of `forLoopBodyNRtRM_map_eq_canonBodyRM_expand`, the typed export
    node seeded from `.reg out` with count operand `.reg c`, renamed by `ρ`, is the
    immediate-shift expansion of `canonNodeRM` at `τ = ρ ∘ σ`. -/
theorem forLoopLcmdNRtRM_map_eq_canonNodeRM_expand {invTys : Ctxt jasminDialect}
    {d : Nat} {out : String} {w n : Nat} {σ ρ : String → String}
    {acc c : String} (invOps : List LOperand)
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hcom : ComOpsPlain update)
    (hσ : LoopRen σ d invTys.length acc (invRegsOf invOps))
    (hρ : NodeRen ρ d acc out c (invRegsOf invOps))
    (hret : ρ (loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
      (2 + invTys.length)).2 = out) :
    (forLoopLcmdNRtRM d acc (.reg out) (.reg c) update invOps (fun _ => none)).map (renRM ρ)
      = (canonNodeRM (ρ ∘ σ) d out c update
          ((loopBodyWalkN d acc (loopIdx d) (invRegsOf invOps) (fun _ => none) update
            (2 + invTys.length)).2 == acc) (invRegsOf invOps)).flatMap immShiftExpand := by
  unfold forLoopLcmdNRtRM canonNodeRM
  rw [List.map_append, guardedFlagLoopLinstrRM_map_renRM, hρ.ctrFix,
    forLoopBodyNRtRM_map_eq_canonBodyRM_expand invOps update hcom hσ hρ hret,
    List.flatMap_append, guardedFlagLoopLinstrRM_flatMap,
    flatMap_immShiftExpand_of_fixed _ (canonSeedsRM_fixed d out c)]
  congr 1
  simp [loopSeedsRM, canonSeedsRM, renRM, renLinstrR, renOperand, hρ.accOut, hρ.outFix,
    hρ.idxFix, hρ.ctrFix, hρ.cntFix]

/-! ## 4. The per-instruction condition on the canonicalised node -/

/-- An immediate shift whose count-in-mnemonic wire the decoder reads back: at
    width `64`, or with a count whose rendering does not end in `:64`. Every other
    op satisfies it. -/
def ImmShiftWireOK : JasminOp → Prop
  | .shrImm w n => w = 64 ∨ hasSuffix ("SHR" ++ ":" ++ toString n) ":64" = false
  | .shlImm w n => w = 64 ∨ hasSuffix ("SHL" ++ ":" ++ toString n) ":64" = false
  | .sarImm w n => w = 64 ∨ hasSuffix ("SAR" ++ ":" ++ toString n) ":64" = false
  | _ => True

/-- Every binding of a `Com` has an op in the fragment's op set whose immediate
    shift, if any, satisfies `ImmShiftWireOK`. -/
def ComExpOK : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop
  | _, _, .ret _ => True
  | _, _, .var e body => OpPlain e.op ∧ ImmShiftWireOK e.op ∧ ComExpOK body

/-- `ComExpOK` implies `ComOpsPlain`. -/
theorem ComExpOK.opsPlain {Γ : Ctxt jasminDialect} {t : JasminTy} :
    (com : Com jasminDialect Γ t) → ComExpOK com → ComOpsPlain com := by
  intro com h
  induction com with
  | ret _ => trivial
  | var e body ih => exact ⟨h.1, ih h.2.2⟩

/-- A renamed `Lopn` fixed by the expansion satisfies the per-instruction
    condition. -/
theorem instrOK_renRM_of_fixed (τ : String → String) {i : LinstrRM} (hl : IsLopn i)
    (hfix : immShiftExpand i = [i]) : InstrOK EqPc immShiftExpand (renRM τ i) := by
  refine JasminLsemExportLower.instrOK_self ?_ (by rw [immShiftExpand_renRM, hfix]; rfl)
  obtain ⟨ds, o, ss, h⟩ := hl
  obtain ⟨wire, tag⟩ := i
  subst h
  exact ⟨_, _, _, rfl⟩

/-- An `opToLinstrR` image is an `Lopn`. -/
theorem isLopn_opToLinstrR (op : JasminOp) (dst : String) (srcs : List LOperand)
    (tag : MemTag) : IsLopn (opToLinstrR op dst srcs, tag) := by
  obtain ⟨o, s, h⟩ := opToLinstrR_dst op dst srcs
  exact ⟨_, _, _, h⟩

/-- Every instruction of the model chain of a `ComExpOK` update, renamed by `τ`,
    satisfies the per-instruction condition of the immediate-shift expansion. -/
theorem straightOpsMem_instrOK (τ : String → String) (nArgs : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (hcom : ComExpOK com) :
    ∀ cd, ∀ i ∈ straightOpsMem nArgs com cd, InstrOK EqPc immShiftExpand (renRM τ i) := by
  induction com with
  | ret v => intro cd i hi; simp [straightOpsMem] at hi
  | var e body ih =>
      obtain ⟨hop, hsh, hbody⟩ := hcom
      intro cd i hi
      simp only [straightOpsMem, List.mem_cons] at hi
      rcases hi with rfl | hi
      · have hreg : ∀ o ∈ exprArgs cd nArgs argName (fun _ => none) e,
            ∃ r, o = LOperand.reg r := exprArgs_isReg e
        split
        · next w n h =>
            rw [h] at hop ⊢
            exact instrOK_renRM_of_fixed τ (isLopn_opToLinstrR _ _ _ _)
              (immShiftExpand_opToLinstrR hop _ _ hreg)
        · next w n h =>
            rw [h] at hop ⊢
            exact instrOK_renRM_of_fixed τ (isLopn_opToLinstrR _ _ _ _)
              (immShiftExpand_opToLinstrR hop _ _ hreg)
        · next w w' h =>
            rw [h] at hop ⊢
            exact instrOK_renRM_of_fixed τ (isLopn_opToLinstrR _ _ _ _)
              (immShiftExpand_opToLinstrR hop _ _ hreg)
        · split
          · next w n s h hs =>
              obtain ⟨r, rfl⟩ := exprArgs_isReg e s (by rw [hs]; simp)
              rw [h] at hsh
              exact instrOK_immShiftExpand_struct (Or.inl rfl) w n _ _ hsh
          · next w n s h hs =>
              obtain ⟨r, rfl⟩ := exprArgs_isReg e s (by rw [hs]; simp)
              rw [h] at hsh
              exact instrOK_immShiftExpand_struct (Or.inr (Or.inl rfl)) w n _ _ hsh
          · next w n s h hs =>
              obtain ⟨r, rfl⟩ := exprArgs_isReg e s (by rw [hs]; simp)
              rw [h] at hsh
              exact instrOK_immShiftExpand_struct (Or.inr (Or.inr rfl)) w n _ _ hsh
          · have htag : memTagOfOp e.op = MemTag.reg none := by
              unfold memTagOfOp; split <;> simp_all
            rw [← htag]
            exact instrOK_renRM_of_fixed τ (isLopn_opToLinstrR _ _ _ _)
              (immShiftExpand_opToLinstrR hop _ _ hreg)
      · exact ih hbody (cd + 1) i hi

/-- An `Lopn` fixed by the expansion satisfies the per-instruction condition. -/
theorem instrOK_of_fixed {i : LinstrRM} (hl : IsLopn i) (hfix : immShiftExpand i = [i]) :
    InstrOK EqPc immShiftExpand i :=
  JasminLsemExportLower.instrOK_self hl hfix

/-- **The canonicalised node satisfies the per-instruction condition.** For a
    `ComExpOK` update every instruction of `canonNodeRM` satisfies the
    per-instruction condition of the immediate-shift expansion. -/
theorem canonNodeRM_instrOK {invTys : Ctxt jasminDialect} (τ : String → String)
    (d : Nat) (out c : String) {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hexp : ComExpOK update) (absent : Bool) (regs : List String) :
    ∀ i ∈ canonNodeRM τ d out c update absent regs, InstrOK EqPc immShiftExpand i := by
  intro i hi
  simp only [canonNodeRM, guardedFlagLoopLinstrRM, flagLoopLinstrRM, flagBackedge,
    canonBodyRM, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at hi
  rcases hi with hi | (rfl | rfl | rfl | ((⟨j, hj, rfl⟩ | (hi | hi) | hi) | rfl | rfl)) | rfl
  · exact instrOK_of_fixed (by
      simp only [canonSeedsRM, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩) (canonSeedsRM_fixed d out c i hi)
  · exact instrOK_of_fixed ⟨_, _, _, rfl⟩ (immShiftExpand_cmp0 _)
  · exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨_, _, rfl, by simp [flagCondCC?]⟩)⟩
  · exact Or.inr ⟨rfl, Or.inl ⟨_, _, rfl⟩⟩
  · exact straightOpsMem_instrOK τ _ update hexp _ j hj
  · refine instrOK_of_fixed ?_ (canonFeedback_fixed out absent i hi)
    unfold canonFeedback at hi
    cases absent
    · simp only [Bool.false_eq_true, if_false, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      subst hi
      exact ⟨_, _, _, rfl⟩
    · simp at hi
  · refine instrOK_of_fixed ?_ (loopAdvanceRM_fixed d i hi)
    simp only [loopAdvanceRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  · refine instrOK_of_fixed ?_ (loopTouchRM_fixed d regs i hi)
    simp only [loopTouchRM, List.mem_map] at hi
    obtain ⟨r, _, rfl⟩ := hi
    exact ⟨_, _, _, rfl⟩
  · exact instrOK_of_fixed ⟨_, _, _, rfl⟩ (immShiftExpand_cmp0 _)
  · exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨_, _, rfl, by simp [flagCondCC?]⟩)⟩
  · exact Or.inr ⟨rfl, Or.inl ⟨_, _, rfl⟩⟩

/-- **A halting run carries to the expansion.** A halting flag-machine run of a
    singleton program all of whose instructions satisfy the per-instruction
    condition of the immediate-shift expansion, started at program counter `0`, is
    matched by a halting run of the expanded program from the same state, ending
    with the same array carrier. -/
theorem lsemFuelMemF_singleton_expand (fn : String) (body : List LinstrRM)
    (hbody : ∀ i ∈ body, InstrOK EqPc immShiftExpand i)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (k : Nat) (t : LstateMF)
    (h : lsemFuelMemF (singletonProgM fn body) k
      { prog := { base := b0, lfn := fn }, zf := zf } = some t) :
    ∃ (k' : Nat) (t' : LstateMF),
      lsemFuelMemF (singletonProgM fn (body.flatMap immShiftExpand)) k'
          { prog := { base := b0, lfn := fn }, zf := zf } = some t'
        ∧ t'.prog.base.larr = t.prog.base.larr := by
  have hP := expProg_immShiftExpand (P := singletonProgM fn body)
    (P' := singletonProgM fn (body.flatMap immShiftExpand)) rfl rfl hbody
  have hR : RelX EqPc immShiftExpand (singletonProgM fn body)
      { prog := { base := b0, lfn := fn }, zf := zf }
      { prog := { base := b0, lfn := fn }, zf := zf } :=
    ⟨rfl, rfl, by
      show b0.lpc = JasminLsemExportLower.pcMap immShiftExpand body b0.lpc
      rw [hpc, JasminLsemExportLower.pcMap_zero], rfl⟩
  obtain ⟨k', t', _, hrun, hRt⟩ := lsemFuelMemF_immShiftExpand hP k hR h
  refine ⟨k', t', hrun, ?_⟩
  have hb : EqPc t.prog.base t'.prog.base := hRt.base
  unfold EqPc at hb
  rw [hb]
  rfl

/-! ## 5. The shipped `mpn_and_n_loop_owned` body -/

/-- The shipped limb body satisfies `ComExpOK`: its two immediate shifts are
    `shlImm 64 0`. -/
theorem binAndUpdate_comExpOK : ComExpOK binAndUpdate := by
  unfold binAndUpdate
  repeat first
    | exact trivial
    | refine ⟨trivial, trivial, ?_⟩
    | refine ⟨trivial, Or.inl rfl, ?_⟩

/-- The return register of the export's body walk of the shipped limb body is
    the store slot's body temporary. -/
theorem binAndUpdate_ret (d : Nat) :
    (loopBodyWalkN d (argName 0) (loopIdx d) [argName 1, argName 2] (fun _ => none)
      binAndUpdate 4).2 = loopReg d 9 := by
  rfl

/-- The node renaming that sends the store slot's body temporary to `argName 0`
    and fixes every other name, with a count register distinct from that
    temporary, is a `NodeRen` of the shipped node. -/
theorem binAnd_nodeRen (d : Nat) (ρ : String → String)
    (hρid : ∀ r, r ≠ loopReg d 9 → ρ r = r) (c : String) (hcR : c ≠ loopReg d 9) :
    NodeRen ρ d (argName 0) (argName 0) c [argName 1, argName 2] where
  accOut := hρid _ (argName_ne_loopReg d 0 9)
  outFix := hρid _ (argName_ne_loopReg d 0 9)
  idxFix := hρid _ (loopIdx_ne_loopReg d d 9)
  ctrFix := hρid _ (loopCtr_ne_loopReg d d 9)
  cntFix := hρid _ hcR
  invFix := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hρid _ (argName_ne_loopReg d 1 9)
    · exact hρid _ (argName_ne_loopReg d 2 9)

/-- **The shipped export node is the expanded canonicalised node.** The typed
    export node of the shipped limb body at the registers
    `MpnLoopFrontEmit.binLprog` passes (accumulator and seed `argName 0`,
    invariant base registers `argName 1`, `argName 2`, count register `c`),
    renamed by a node renaming `ρ` that sends the store slot's body temporary to
    `argName 0` and fixes every other name, is the immediate-shift expansion of the
    canonicalised node at `ρ ∘ logicSigma d`. -/
theorem binAnd_export_node_eq (d : Nat) (ρ : String → String)
    (hρid : ∀ r, r ≠ loopReg d 9 → ρ r = r) (hρs : ρ (loopReg d 9) = argName 0)
    (c : String) (hcR : c ≠ loopReg d 9) :
    (forLoopLcmdNRtRM d (argName 0) (.reg (argName 0)) (.reg c) binAndUpdate
        [.reg (argName 1), .reg (argName 2)] (fun _ => none)).map (renRM ρ)
      = (canonNodeRM (ρ ∘ logicSigma d) d (argName 0) c binAndUpdate
          (loopReg d 9 == argName 0) [argName 1, argName 2]).flatMap immShiftExpand := by
  have h := forLoopLcmdNRtRM_map_eq_canonNodeRM_expand (out := argName 0) (c := c)
    [.reg (argName 1), .reg (argName 2)] binAndUpdate
    (ComExpOK.opsPlain _ binAndUpdate_comExpOK) (logicSigma_loopRen d)
    (binAnd_nodeRen d ρ hρid c hcR)
    ((congrArg ρ (binAndUpdate_ret d)).trans hρs)
  exact h

/-- **The shipped export node computes the model loop.** The typed export node
    of the shipped `mpn_and_n_loop_owned` limb body at the registers
    `MpnLoopFrontEmit.binLprog` passes, renamed by a node renaming `ρ` that sends
    the store slot's body temporary to `argName 0` and fixes every other name, run
    on the flag machine from program counter `0` with the seed agreement, readable
    invariant base registers and the trip count in `c`, halts with the array at
    `argName 0` decoding to the source fold of the limb body. -/
theorem binAnd_export_machine_shipped (d : Nat) (ρ : String → String)
    (hρid : ∀ r, r ≠ loopReg d 9 → ρ r = r) (hρs : ρ (loopReg d 9) = argName 0)
    (invs : Ctxt.Valuation ([AN, AN] : Ctxt jasminDialect))
    (fn c : String) (hc : c ≠ loopIdx d) (hcR : c ≠ loopReg d 9)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (arr0 : Fin N → BitVec 64)
    (hseed : StoreAgreesM (([AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN] : Ctxt jasminDialect).length + 2)
      (pullM (ρ ∘ logicSigma d) (b0.setReg (loopIdx d) (0#64)))
      (tripValArrMN invs 0 arr0))
    (hinv : ∀ j, j < ([AN, AN] : Ctxt jasminDialect).length →
      (b0.reg.getW ((ρ ∘ logicSigma d) (argName j)) 64).isSome)
    (m : Nat) (hm64 : m < 2 ^ 64)
    (hcnt : b0.reg.getW c 64 = some (BitVec.ofNat 64 m)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          ((forLoopLcmdNRtRM d (argName 0) (.reg (argName 0)) (.reg c) binAndUpdate
            [.reg (argName 1), .reg (argName 2)] (fun _ => none)).map (renRM ρ))) k
          { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base (argName 0) 64 N
            = some (JLoopBodyN.denote ⟨m, binAndUpdate⟩ invs arr0) := by
  have hregs : ∀ r ∈ [argName 1, argName 2], ∃ j,
      j < ([AN, AN] : Ctxt jasminDialect).length ∧ r = (ρ ∘ logicSigma d) (argName j) := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨1, by decide, ?_⟩
      show _ = ρ (logicSigma d (argName 1))
      rw [logicSigma_argName1, hρid _ (argName_ne_loopReg d 1 9)]
    · refine ⟨0, by decide, ?_⟩
      show _ = ρ (logicSigma d (argName 0))
      rw [logicSigma_argName0, hρid _ (argName_ne_loopReg d 2 9)]
  obtain ⟨k, t, hrun, hdec⟩ := binAnd_canon_machine_export d ρ hρid hρs
    (loopReg d 9 == argName 0) [argName 1, argName 2] hregs invs fn c hc b0 zf hpc arr0
    hseed hinv m hm64 hcnt
  obtain ⟨k', t', hrun', hlarr⟩ := lsemFuelMemF_singleton_expand fn _
    (canonNodeRM_instrOK _ d _ c binAndUpdate binAndUpdate_comExpOK _ _) b0 zf hpc k t hrun
  refine ⟨k', t', ?_, ?_⟩
  · rw [binAnd_export_node_eq d ρ hρid hρs c hcR]
    exact hrun'
  · rw [decodeArrM_congr_larr _ _ hlarr]
    exact hdec

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd
