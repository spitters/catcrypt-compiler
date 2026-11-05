/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW

@[expose] public section

set_option autoImplicit false

/-!
# The printed class with carry chains is encodable

The gated encoder `LprogBytes.encodeLfundefBytesChecked`, through which the region back end
lays down the bytes of a printed body, returns bytes only on a body that `encodableLcmd`
accepts: every instruction carries no bytes by construction (`carriesNoBytes`) or has a
nonempty encoding. This module proves that every body of the printed class with carry chains
`printedAddrWB` passes this check, so that the gated encoder does not refuse a body the
printed class accepts.

Every arm of `instrOKWB` has a byte lemma: the encoder lays down the concatenation of the
pieces of the arm, and each piece decodes in front of every continuation (`PieceDec`). A
piece that decodes in front of the empty continuation has bytes (`bytes_ne_nil_of_pieceDec`), so
an arm with at least one piece has a nonempty encoding. Every arm has a piece except the
count-`0` shift `SHL:0:64 D, D` of a name in place, which carries no bytes by construction.

## Main results

* `bytes_ne_nil_of_pieceDec`: a decoding piece has bytes.
* `encodableLinstrR_of_pieces`: an `Lopn` laid down as a nonempty list of decoding pieces is
  encodable.
* `encodable_of_instrOKWB`: an instruction `instrOKWB` accepts is encodable, under every body
  and all body parameters.
* `encodable_of_printedAddrWB`: a body of `printedAddrWB` passes `encodableLcmd`.

## The address forms of the class

The cell arms `MArm` and the indexed arms `AArm.ldx`, `AArm.stx` take every general-purpose
base, `RBP` and `R13` included: the encoder lays down the forced zero `disp8` of a base whose
low three bits are `5` (`ScalarEncoder.memTail`, `LprogBytes.sibTail`), and the decoder reads
it (`decodeMemTail_memTail32`, `DecodeGen.decodeLinstr_loadIdx8_sib`). The indexed arms are at
stride `8`; the address machine `VIR.JasminLsemAddrMem.fstepA` reads and writes a whole word at
every stride, while the encoder lays down a narrow access at the strides `1`, `2`, `4`
(`LprogBytes.encLoadIdx`, `LprogBytes.encStoreIdx`).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (movImmStruct? movImmStruct?_spec
  isMovImmMnem isMovImmMnem_iff)

/-- **A decoding piece has bytes**: the decoder reads no instruction off the empty stream. -/
theorem bytes_ne_nil_of_pieceDec {q : List (BitVec 8) × JInstr 64} (h : PieceDec q) :
    q.1 ≠ [] := by
  intro h0
  have h1 := h []
  rw [h0] at h1
  simp [decodeLinstr] at h1

/-- **An `Lopn` laid down as a nonempty list of decoding pieces is encodable.** -/
theorem encodableLinstrR_of_pieces {F W Q : Nat} {ds : List LOperand} {o : String}
    {ss : List LOperand} {pcs : List (List (BitVec 8) × JInstr 64)}
    (hb : encodeLopn F W (.Lopn ds o ss) Q = pcs.flatMap Prod.fst)
    (hp : ∀ q ∈ pcs, PieceDec q) (hne : pcs ≠ []) :
    encodableLinstrR F W (.Lopn ds o ss) Q = true := by
  obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hne
  have h0 := bytes_ne_nil_of_pieceDec (hp q List.mem_cons_self)
  have hne' : encodeLopn F W (.Lopn ds o ss) Q ≠ [] := by
    rw [hb, List.flatMap_cons]
    exact fun h => h0 (List.append_eq_nil_iff.mp h).1
  simp only [encodableLinstrR, encodeLinstrR, Bool.or_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff]
  exact Or.inr hne'

/-- An instruction equal to an `Lopn` laid down as a nonempty list of decoding pieces is
    encodable. -/
theorem encodableLinstrR_of_eq {F W Q : Nat} {i j : LinstrR}
    {pcs : List (List (BitVec 8) × JInstr 64)} (he : j = i)
    (hb : encodeLopn F W j Q = pcs.flatMap Prod.fst) (hp : ∀ q ∈ pcs, PieceDec q)
    (hne : pcs ≠ []) (hj : ∃ ds o ss, j = .Lopn ds o ss) :
    encodableLinstrR F W i Q = true := by
  obtain ⟨ds, o, ss, rfl⟩ := hj
  subst he
  exact encodableLinstrR_of_pieces hb hp hne

/-- The pieces of a slot carry arm are not empty. -/
theorem SArm.pieces_ne_nil (P : Params) (c : SArm) : c.pieces P ≠ [] := by
  cases c <;> simp only [SArm.pieces, cPre] <;> (try split) <;> simp

/-- The pieces of a carry arm are not empty. -/
theorem CArm.pieces_ne_nil (c : CArm) : c.pieces ≠ [] := by
  cases c <;> simp [CArm.pieces]

/-- The pieces of a cell arm are not empty. -/
theorem MArm.pieces_ne_nil (m : MArm) : m.pieces ≠ [] := by
  cases m <;> simp [MArm.pieces]

/-- An arm of `DecodePrintedAddr` whose conditions hold has a piece, or is the count-`0` shift
    `m D, D` of a name in place, `m` the mnemonic `SHL:0:64`. -/
theorem AArm.pieces_ne_nil_or (P : Params) (a : AArm) (h : a.ok P = true) :
    a.pieces P ≠ [] ∨ ∃ m D, a = .reg (.shl0 m D D) ∧ gpOk D = true
      ∧ isIdentityTagShift m = true := by
  cases a with
  | reg b =>
    simp only [AArm.ok, Bool.and_eq_true] at h
    have hb := h.1.2
    cases b with
    | alu m D S =>
      left
      simp only [Arm.ok, Bool.and_eq_true, Option.isSome_iff_exists] at hb
      obtain ⟨⟨⟨⟨op, mk⟩, hm⟩, -⟩, -⟩ := hb
      simp [AArm.pieces, Arm.pieces, hm]
    | aluI m D v =>
      left
      simp only [Arm.ok, Bool.and_eq_true, Option.isSome_iff_exists] at hb
      obtain ⟨⟨⟨⟨op, mk⟩, hm⟩, -⟩, -⟩ := hb
      simp [AArm.pieces, Arm.pieces, hm]
    | shl0 m D S =>
      by_cases hDS : D = S
      · subst hDS
        right
        simp only [Arm.ok, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
          beq_iff_eq] at hb
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, -⟩, hco, -⟩, -⟩, -⟩, -⟩, hext⟩, -⟩, hcnt⟩, -⟩ := hb
        refine ⟨m, D, rfl, hD, ?_⟩
        simp only [isIdentityTagShift, hco, hext, hcnt, Bool.not_false, Option.isSome_some,
          beq_self_eq_true, Bool.and_self]
      · left
        simp [AArm.pieces, Arm.pieces, hDS]
    | shr m D S =>
      left
      simp only [AArm.pieces, Arm.pieces]
      split <;> simp
    | _ => left; simp [AArm.pieces, Arm.pieces]
  | zero B n =>
    left
    simp only [AArm.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [AArm.pieces, zeroPieces, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    omega
  | _ => left; simp [AArm.pieces, Arm.pieces, stPieces]

/-- **An instruction of the printed class with carry chains is encodable**: an instruction
    `instrOKWB` accepts carries no bytes by construction or has a nonempty encoding, under
    every body and all body parameters. -/
theorem encodable_of_instrOKWB (body : Lcmd) (P : Params) (i : LinstrR)
    (h : instrOKWB body P i = true) :
    encodableLinstrR P.frame P.spillW i P.qsaveB = true := by
  match i, h with
  | .Llabel _ _, _ => rfl
  | .Lcond c l, h =>
    cases c with
    | reg cc =>
      simp only [encodableLinstrR, encodeLinstrR, Bool.or_eq_true, Bool.not_eq_true',
        List.isEmpty_eq_false_iff]
      right
      split <;> simp [encJcc8, encJcc32]
    | _ => simp [instrOKWB] at h
  | .Lopn ds o ss, h =>
    simp only [instrOKWB] at h
    split at h
    · -- a width-carrying cast
      rename_i d a m w hK
      obtain ⟨o', he, hm, -⟩ := classifyK_spec hK
      simp only [castOk, Bool.and_eq_true] at h
      obtain ⟨hb, hp⟩ := castBytes P o' d a m hm h.1 h.2
      exact encodableLinstrR_of_eq he.symm hb hp (by simp [castPieces]) ⟨_, _, _, rfl⟩
    rename_i hK
    split at h
    · -- an untagged immediate move
      rename_i D n hmv
      obtain ⟨o', hia0⟩ := movImmStruct?_spec hmv
      simp only [LinstrR.Lopn.injEq] at hia0
      obtain ⟨hds, rfl, hss⟩ := hia0
      subst hds hss
      have hmi : isMovImmMnem o = true := by simpa [movImmStruct?] using hmv
      have henc : encodeLopn P.frame P.spillW (.Lopn [.reg D] o [.imm n]) P.qsaveB
          = encodeLopn P.frame P.spillW (.Lopn [.reg D] "MOV" [.imm n]) P.qsaveB := by
        rcases isMovImmMnem_iff.1 hmi with rfl | ⟨w, hw, rfl⟩
        · rfl
        · exact encodeLopn_retag32 _ _ _ hw (by decide) (by decide +kernel) (by decide +kernel)
            _ _
      obtain ⟨hb, hp⟩ := imm32Bytes P D n h
      exact encodableLinstrR_of_pieces (henc.trans hb) hp (by simp [zPieces])
    rename_i hmv
    split at h
    · -- a slot carry arm
      rename_i c hcl
      obtain ⟨hb, hp⟩ := SArm.bytes P c h
      rw [← classifyS_instr hcl]
      exact encodableLinstrR_of_eq rfl hb hp (SArm.pieces_ne_nil P c)
        (by cases c <;> exact ⟨_, _, _, rfl⟩)
    rename_i hS
    split at h
    · -- a carry arm
      rename_i c hcl
      obtain ⟨hb, hp⟩ := CArm.bytes P c h
      rw [← classifyC_instr hcl]
      exact encodableLinstrR_of_eq rfl hb hp (CArm.pieces_ne_nil c)
        (by cases c <;> exact ⟨_, _, _, rfl⟩)
    rename_i hC
    split at h
    · -- a cell arm
      rename_i m hcl
      obtain ⟨hb, hp⟩ := MArm.bytes P m h
      rw [← classifyM_instr hcl]
      exact encodableLinstrR_of_eq rfl hb hp (MArm.pieces_ne_nil m)
        (by cases m <;> exact ⟨_, _, _, rfl⟩)
    rename_i hM
    split at h
    · -- an immediate store into a frame slot
      rename_i q v hcl
      obtain ⟨hb, hp⟩ := iBytes P q v h
      rw [classifyI_instr hcl]
      exact encodableLinstrR_of_pieces hb hp (by unfold iPieces; split <;> simp)
    rename_i hI
    split at h
    · -- a wide immediate
      rename_i D v hcl
      obtain ⟨hb, hp⟩ := lBytes P D v h
      rw [(classifyL_instr hcl).1]
      exact encodableLinstrR_of_pieces hb hp (by simp [lPieces])
    rename_i hL
    split at h
    · -- a select
      rename_i D C A B hcl
      rw [classifyV_instr hcl]
      rcases Bool.or_eq_true_iff.mp h with hv | h
      · obtain ⟨hb, hp⟩ := vBytes P D C A B hv
        exact encodableLinstrR_of_pieces hb hp (by unfold vPieces; split <;> simp)
      rcases Bool.or_eq_true_iff.mp h with hv | hv
      · obtain ⟨hb, hp⟩ := vtBytes P D C A B hv
        exact encodableLinstrR_of_pieces hb hp (by simp [vtPieces])
      · by_cases hAD : A = D
        · subst hAD
          obtain ⟨hb, hp⟩ := veBytes P A C B hv
          exact encodableLinstrR_of_pieces hb hp (by simp [vePieces])
        · obtain ⟨hb, hp⟩ := vfBytes P D C A B hv hAD
          exact encodableLinstrR_of_pieces hb hp (by simp [vfPieces])
    rename_i hV
    split at h
    · -- a materialised comparison
      rename_i n D A B hcl
      obtain ⟨hb, hp⟩ := eBytes P n D A B h
      rw [classifyE_instr hcl]
      exact encodableLinstrR_of_pieces hb hp (by simp [ePieces])
    rename_i hE
    split at h
    · -- a register-count shift
      rename_i l D A B hcl
      obtain ⟨hb, hp⟩ := xBytes P l D A B h
      rw [classifyX_instr hcl]
      exact encodableLinstrR_of_pieces hb hp (by simp [xPieces])
    rename_i hX
    split at h
    · -- a materialised comparison against an immediate
      rename_i n D A v hcl
      obtain ⟨hb, hp⟩ := eiBytes P n D A v h
      rw [classifyEI_instr hcl]
      exact encodableLinstrR_of_pieces hb hp (by simp [eiPieces])
    rename_i hEI
    split at h
    · -- an arithmetic right shift by an immediate
      rename_i D k hcl
      obtain ⟨hb, hp⟩ := rBytes_encode P D k h
      rw [classifyR_instr hcl]
      exact encodableLinstrR_of_pieces hb hp (by simp [rPieces])
    rename_i hR
    split at h
    · -- an arm of `DecodePrintedAddr`
      rename_i a hcl
      have hia := classifyA_instr hcl
      obtain ⟨hb, hp⟩ := AArm.bytes P a h
      rcases AArm.pieces_ne_nil_or P a h with hne | ⟨m, D, rfl, hD, hid⟩
      · rw [← hia]
        refine encodableLinstrR_of_eq rfl hb hp hne ?_
        cases a with
        | reg b => cases b <;> exact ⟨_, _, _, rfl⟩
        | _ => exact ⟨_, _, _, rfl⟩
      · rw [← hia]
        have hg := (gpFacts hD).isGp
        simp only [AArm.instr, Arm.instr, encodableLinstrR, carriesNoBytes, beq_self_eq_true,
          hg, hid, Bool.and_self, Bool.or_true, Bool.true_or]
    · exact absurd h (by simp)
  | .Lret, h => simp [instrOKWB] at h
  | .Lalign, h => simp [instrOKWB] at h
  | .Lgoto _, h => simp [instrOKWB] at h
  | .Lcall _ _, h => simp [instrOKWB] at h
  | .Lsyscall _, h => simp [instrOKWB] at h
  | .Ligoto _, h => simp [instrOKWB] at h
  | .LstoreLabel _ _, h => simp [instrOKWB] at h

/-- **The printed class with carry chains is encodable**: every body of `printedAddrWB` passes
    `encodableLcmd`, so the gated encoder `encodeLfundefBytesChecked` returns its bytes. -/
theorem encodable_of_printedAddrWB {body : Lcmd} (h : printedAddrWB body = true) :
    encodableLcmd body = true := by
  obtain ⟨shs, hF⟩ := bodyFactsW_of h
  unfold encodableLcmd
  rw [List.all_eq_true]
  intro i hi
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
  by_cases hkl : k + 1 < body.length
  · exact encodable_of_instrOKWB body (Params.ofBody body) _ (hF.instr k hkl)
  · have hk1 : k = body.length - 1 := by omega
    subst hk1
    rw [hF.last]
    rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
