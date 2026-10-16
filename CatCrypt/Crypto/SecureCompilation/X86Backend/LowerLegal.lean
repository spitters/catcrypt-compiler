/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeComplete
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Proofs

@[expose] public section

set_option autoImplicit false

/-!
# The lowering after register allocation emits legal forms

`physPositionEmit` is the per-position expansion of `physBodyWithStores`: the inline
argument loads, the register-allocated expansion of the virtual instruction, the pointer
reloads after a call and the inline output store. This module proves that every instruction
it emits has a legal form `LegalForm` at the x86 encoder `x86Enc`, over operands the
allocation resolves, and that the load forwarding `loadCSE` preserves legal forms, so the
forwarded body is encodable.

## The lowering families

The expansion emits, by arm:

* the two-address binops (`isTwoAddrBinop`: `ADD`, `SUB`, `MUL`, `AND`, `OR`, `XOR`,
  `SHL`, `SHR`) through `lowerTwoAddr` and `lowerTwoAddrShiftImm`: register moves, moves of
  an immediate, the operation over two registers (`LegalForm.alu`, or `LegalForm.shiftReg`
  for a shift by a register), and against an immediate (`LegalForm.aluImm`);
* the native count-in-tag shifts through `lowerNativeShiftRotate`: register moves and the
  one-source operation (`LegalForm.unary`);
* the loads `LOAD`/`LOADIDX` through `legalizeMemLoad` and the memref base reload: moves,
  the load (`LegalForm.memMov`) and the register-indexed load (`LegalForm.sibLoad`);
* the stores `STOREIDX` through `legalizeMemStoreK`: moves, the displacement store
  (`LegalForm.memMov`), the address computation `LEA` (`LegalForm.sibLoad`) and the
  register-indexed store (`LegalForm.sibStore`);
* the selects and comparisons through `legalizeSpillDst`: the scratch select and the scratch
  comparison, and otherwise the remapped instruction;
* the one-source moves through `legalizeOneSrc`, and otherwise the remapped instruction;
* the remapped instruction of every other shape (the carry chains, the flag
  materialisations, the widening multiplication, the control transfers);
* the ABI moves of the argument loads, the post-call reloads and the output store.

The arms that emit the remapped instruction unchanged do not legalise its spilled operands;
there the legal form of the remapped instruction is a hypothesis (`PosOk`).

## Main definitions

* `ValOk`: a source a move may copy: an allocated operand, or an immediate the encoder moves
  into a slot.
* `LoadSrc`: the source of a load: a resolving name under `x86MemMov`, or a
  register-indexed address of allocated names under `LOADIDX`.
* `SpillDstOk`: the hypotheses of the arm `legalizeSpillDst`.
* `PosOk`: the hypotheses of one position on the virtual instruction and the operand map.

## Main results

* `legalizeMov_legal`, `legalizeBinop_legal`, `lowerTwoAddr_legal`,
  `lowerTwoAddrShiftImm_legal`, `lowerNativeShiftRotate_legal`, `legalizeMemLoad_legal`,
  `legalizeMemStoreK_legal`, `legalizeOneSrc_legal`, `legalizeSpillDst_legal`: the
  lowerers and legalisers emit legal forms.
* `lower_legal`: every instruction of one position of `physPositionEmit` has a legal form.
* `physBodyWithStores_legal`: every instruction of `physBodyWithStores` has a legal form.
* `lower_legal_loadCSE`: so does every instruction of its forwarding by `loadCSE`;
  `encodable_loadCSE_physBodyWithStores`: the forwarded body is encodable.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowerLegal

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeComplete
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (isMovMnem LegalForm)

/-- The legal forms of the x86 encoder in the context `(F, W, Q)`. -/
abbrev LF (F W Q : Nat) (i : LinstrR) : Prop := LegalForm X86Isa.x86Isa x86Enc (F, W, Q) i

/-! ## Operands -/

/-- A source a move may copy: an allocated operand, or an immediate the encoder moves into a
    spill slot under the move mnemonic `mov`. -/
def ValOk (F W Q : Nat) (mov : String) (o : LOperand) : Prop :=
  AllocOp F W Q o ∨ ∃ v, o = .imm v ∧ x86SlotImm mov v = true

variable {F W Q : Nat}

theorem isGpName_reloadScratch : isGpName reloadScratch = true := isGpName_R15
theorem isGpName_reloadScratch2 : isGpName reloadScratch2 = true := isGpName_R14

theorem allocOp_of_gp {n : String} (h : isGpName n = true) : AllocOp F W Q (.reg n) :=
  allocOp_gp h

theorem gp_of_allocOp {n : String} (h : AllocOp F W Q (.reg n))
    (hs : (LOperand.reg n).isSpill = false) : isGpName n = true :=
  isGpName_of_allocOp_not_spill h hs

theorem isSpill_imm (v : Nat) : (LOperand.imm v).isSpill = false := rfl

/-- A move from an allocated operand into a general-purpose register has a legal form. -/
theorem lf_mov_left {mn r n : String} (hm : isMovMnem mn = true) (hr : isGpName r = true)
    (hn : AllocOp F W Q (.reg n)) : LF F W Q (.Lopn [.reg r] mn [.reg n]) :=
  x86Enc_complete.legalForm_mov_left (c := (F, W, Q)) hm hr (allocOp_iff_allocOpI.1 hn)

/-- A move from a general-purpose register into an allocated operand has a legal form. -/
theorem lf_mov_right {mn r n : String} (hm : isMovMnem mn = true) (hr : isGpName r = true)
    (hn : AllocOp F W Q (.reg n)) : LF F W Q (.Lopn [.reg n] mn [.reg r]) :=
  x86Enc_complete.legalForm_mov_right (c := (F, W, Q)) hm hr (allocOp_iff_allocOpI.1 hn)

/-- A move from a resolving name into a general-purpose register has a legal form. -/
theorem lf_mov_res_left {mn r n : String} (hm : isMovMnem mn = true) (hr : isGpName r = true)
    (hn : OpResolves F W Q n) : LF F W Q (.Lopn [.reg r] mn [.reg n]) :=
  .mov mn r n hm (Or.inl hr) hn (by simp [x86Enc, encMemName_of_isGpName hr])

/-- A move from a general-purpose register into a resolving name has a legal form. -/
theorem lf_mov_res_right {mn r n : String} (hm : isMovMnem mn = true) (hr : isGpName r = true)
    (hn : OpResolves F W Q n) : LF F W Q (.Lopn [.reg n] mn [.reg r]) :=
  .mov mn n r hm hn (Or.inl hr) (by simp [x86Enc, encMemName_of_isGpName hr])

/-- A move of an immediate into an allocated operand has a legal form when the encoder moves
    the immediate into a slot. -/
theorem lf_movImm {mn dn : String} {v : Nat} (hm : isMovMnem mn = true)
    (hd : AllocOp F W Q (.reg dn)) (hv : x86SlotImm mn v = true) :
    LF F W Q (.Lopn [.reg dn] mn [.imm v]) := by
  obtain ⟨m, hm', hc⟩ := hd
  cases hm'
  rcases hc with hg | ⟨-, hs⟩
  · exact .movImmReg mn dn v hm hg
  · exact .movImmSlot mn dn v hm hs hv

/-- A two-address operation over two general-purpose registers has a legal form when the
    encoder builds it as an operation of `x86Alu` or a shift of `x86ShiftReg`. -/
theorem lf_binReg {opn r s : String} (ho : x86Alu opn = true ∨ x86ShiftReg opn = true)
    (hr : isGpName r = true) (hs : isGpName s = true) :
    LF F W Q (.Lopn [.reg r] opn [.reg r, .reg s]) := by
  rcases ho with ho | ho
  · exact .alu opn r s ho hr hs
  · exact .shiftReg opn r r s ho hr hr hs

/-- The resolving names include the `mem.*` cells over a general-purpose base. -/
theorem opResolves_memName {b : String} (hb : isGpName b = true) (off : Nat) :
    OpResolves F W Q (memName b off) := by
  refine Or.inr (Or.inr ?_)
  rw [GatherMemOps.parseMemNameGp_of_memNameParts (ConstIndexFold.memNameParts_memName hb off)
    hb]
  rfl

/-! ## The register copy and the two-address operation -/

/-- **A legalised register copy into an allocated operand from a source a move may copy has
    legal forms.** -/
theorem legalizeMov_legal {d s : LOperand} {mov : String} (hm : isMovMnem mov = true)
    (hd : AllocOp F W Q d) (hs : ValOk F W Q mov s) :
    ∀ i ∈ legalizeMov d s mov, LF F W Q i := by
  rcases hs with hs | ⟨v, rfl, hv⟩
  · exact x86Enc_complete.legalizeMovI_legal (c := (F, W, Q)) hm (allocOp_iff_allocOpI.1 hd)
      (allocOp_iff_allocOpI.1 hs)
  · obtain ⟨dn, rfl, hd'⟩ := hd
    intro i hi
    simp only [legalizeMov, isSpill_imm, Bool.and_false, Bool.false_eq_true, if_false,
      List.mem_singleton] at hi
    subst hi
    exact lf_movImm hm ⟨dn, rfl, hd'⟩ hv

/-- **The two-address legalisation has legal forms**: on an allocated destination and a
    source that is an allocated operand under an operation of `x86Alu` or `x86ShiftReg`, or
    an immediate under `x86AluImm`, every instruction of `legalizeBinop` has a legal form. -/
theorem legalizeBinop_legal {dst src : LOperand} {opn mov : String}
    (hm : isMovMnem mov = true) (hd : AllocOp F W Q dst)
    (hsrc : (AllocOp F W Q src ∧ (x86Alu opn = true ∨ x86ShiftReg opn = true)) ∨
      ∃ v, src = .imm v ∧ x86AluImm opn v = true) :
    ∀ i ∈ legalizeBinop dst src opn mov, LF F W Q i := by
  obtain ⟨dn, rfl, hd'⟩ := hd
  have hd : AllocOp F W Q (.reg dn) := ⟨dn, rfl, hd'⟩
  have h15 := isGpName_reloadScratch
  have h14 := isGpName_reloadScratch2
  intro i hi
  unfold legalizeBinop at hi
  rcases hsrc with ⟨⟨sn, rfl, hs'⟩, ho⟩ | ⟨v, rfl, hv⟩
  · have hs : AllocOp F W Q (.reg sn) := ⟨sn, rfl, hs'⟩
    cases hds : (LOperand.reg dn).isSpill <;> cases hss : (LOperand.reg sn).isSpill <;>
      simp only [hds, hss, List.mem_cons, List.not_mem_nil, or_false] at hi
    · subst hi
      exact lf_binReg ho (gp_of_allocOp hd hds) (gp_of_allocOp hs hss)
    · rcases hi with rfl | rfl
      · exact lf_mov_left hm h15 hs
      · exact lf_binReg ho (gp_of_allocOp hd hds) h15
    · rcases hi with rfl | rfl | rfl
      · exact lf_mov_left hm h15 hd
      · exact lf_binReg ho h15 (gp_of_allocOp hs hss)
      · exact lf_mov_right hm h15 hd
    · rcases hi with rfl | rfl | rfl | rfl
      · exact lf_mov_left hm h15 hd
      · exact lf_mov_left hm h14 hs
      · exact lf_binReg ho h15 h14
      · exact lf_mov_right hm h15 hd
  · cases hds : (LOperand.reg dn).isSpill <;>
      simp only [hds, isSpill_imm, List.mem_cons, List.not_mem_nil, or_false] at hi
    · subst hi
      exact .aluImm opn dn v hv (gp_of_allocOp hd hds)
    · rcases hi with rfl | rfl | rfl
      · exact lf_mov_left hm h15 hd
      · exact .aluImm opn _ v hv h15
      · exact lf_mov_right hm h15 hd

/-- The prelude of `materializeWideImm` has legal forms. -/
theorem materializeWideImm_pre_legal (s1 : LOperand) (mov : String) :
    ∀ i ∈ (materializeWideImm s1 mov).1, LF F W Q i := by
  intro i hi
  unfold materializeWideImm at hi
  split at hi
  · split_ifs at hi
    · simp only [List.mem_singleton] at hi
      subst hi
      exact .movImmReg _ _ _ (by decide +kernel) isGpName_reloadScratch2
    · simp at hi
  · simp at hi

/-- The operand of `materializeWideImm` is the scratch `R14`, or the operand itself, which,
    when it is an immediate under `MOV:64`, is below `2^31`. -/
theorem materializeWideImm_snd (s1 : LOperand) (mov : String) :
    (materializeWideImm s1 mov).2 = .reg reloadScratch2 ∨
      ((materializeWideImm s1 mov).2 = s1 ∧
        ∀ v, s1 = .imm v → mov = "MOV:64" → v < 2 ^ 31) := by
  unfold materializeWideImm
  split
  · next v =>
    split_ifs with h
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, fun v' hv' _ => by cases hv'; omega⟩
  · next h =>
    refine Or.inr ⟨rfl, fun v hv hmov => ?_⟩
    subst hv hmov
    exact (h v rfl rfl).elim

/-- **The two-address lowering has legal forms**: on an allocated destination, a first source
    a move may copy, and a second source that is an allocated operand or an immediate, every
    instruction of `lowerTwoAddr` has a legal form when the operation is of `x86Alu` or
    `x86ShiftReg` over registers, and of `x86AluImm` on each immediate that is below `2^31`
    under `MOV:64`. -/
theorem lowerTwoAddr_legal {dst s0 s1 : LOperand} {opn mov : String}
    (hm : isMovMnem mov = true) (hd : AllocOp F W Q dst) (h0 : ValOk F W Q mov s0)
    (h1 : AllocOp F W Q s1 ∨ ∃ v, s1 = .imm v)
    (hreg : x86Alu opn = true ∨ x86ShiftReg opn = true)
    (himm : ∀ v, s1 = .imm v → (mov = "MOV:64" → v < 2 ^ 31) → x86AluImm opn v = true) :
    ∀ i ∈ lowerTwoAddr dst s0 s1 opn mov, LF F W Q i := by
  have hpre := materializeWideImm_pre_legal (F := F) (W := W) (Q := Q) s1 mov
  have hbin : ∀ i ∈ legalizeBinop dst (materializeWideImm s1 mov).2 opn mov, LF F W Q i := by
    apply legalizeBinop_legal hm hd
    rcases materializeWideImm_snd s1 mov with h | ⟨h, hlt⟩
    · rw [h]
      exact Or.inl ⟨allocOp_of_gp isGpName_reloadScratch2, hreg⟩
    · rw [h]
      rcases h1 with h1 | ⟨v, rfl⟩
      · exact Or.inl ⟨h1, hreg⟩
      · exact Or.inr ⟨v, rfl, himm v rfl (hlt v rfl)⟩
  intro i hi
  unfold lowerTwoAddr at hi
  split_ifs at hi
  · rcases List.mem_append.1 hi with hi | hi
    · exact hpre i hi
    · exact hbin i hi
  · rcases List.mem_append.1 hi with hi | hi
    · rcases List.mem_append.1 hi with hi | hi
      · exact legalizeMov_legal hm hd h0 i hi
      · exact hpre i hi
    · exact hbin i hi

/-- **The immediate-shift lowering has legal forms**: on an allocated destination, a source
    a move may copy and an operation of `x86AluImm` at the count, every instruction of
    `lowerTwoAddrShiftImm` has a legal form. -/
theorem lowerTwoAddrShiftImm_legal {dst s0 : LOperand} {v : Nat} {opn mov : String}
    (hm : isMovMnem mov = true) (hd : AllocOp F W Q dst) (h0 : ValOk F W Q mov s0)
    (hv : x86AluImm opn v = true) :
    ∀ i ∈ lowerTwoAddrShiftImm dst s0 v opn mov, LF F W Q i := by
  have h15 := isGpName_reloadScratch
  obtain ⟨dn, rfl, hd'⟩ := hd
  have hd : AllocOp F W Q (.reg dn) := ⟨dn, rfl, hd'⟩
  intro i hi
  unfold lowerTwoAddrShiftImm at hi
  split_ifs at hi with hs he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rcases h0 with ⟨sn, rfl, hs'⟩ | ⟨w, rfl, -⟩
      · exact lf_mov_left hm h15 ⟨sn, rfl, hs'⟩
      · exact .movImmReg _ _ _ hm h15
    · exact .aluImm opn _ v hv h15
    · exact lf_mov_right hm h15 hd
  · simp only [List.mem_singleton] at hi
    subst hi
    exact .aluImm opn dn v hv (gp_of_allocOp hd (by simpa using hs))
  · rcases List.mem_append.1 hi with hi | hi
    · exact legalizeMov_legal hm hd h0 i hi
    · simp only [List.mem_singleton] at hi
      subst hi
      exact .aluImm opn dn v hv (gp_of_allocOp hd (by simpa using hs))

/-- **The native shift lowering has legal forms**: on allocated operands and an operation of
    `x86Unary`, every instruction of `lowerNativeShiftRotate` has a legal form. -/
theorem lowerNativeShiftRotate_legal {d s : LOperand} {opn mov : String}
    (hm : isMovMnem mov = true) (hd : AllocOp F W Q d) (hs : AllocOp F W Q s)
    (ho : x86Unary opn = true) :
    ∀ i ∈ lowerNativeShiftRotate d s opn mov, LF F W Q i := by
  have h15 := isGpName_reloadScratch
  obtain ⟨dn, rfl, hd'⟩ := hd
  obtain ⟨sn, rfl, hs'⟩ := hs
  have hd : AllocOp F W Q (.reg dn) := ⟨dn, rfl, hd'⟩
  have hs : AllocOp F W Q (.reg sn) := ⟨sn, rfl, hs'⟩
  intro i hi
  unfold lowerNativeShiftRotate at hi
  split_ifs at hi with hsp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact lf_mov_left hm h15 hs
    · exact .unary opn _ _ ho h15 h15
    · exact lf_mov_right hm h15 hd
  · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hsp
    simp only [List.mem_singleton] at hi
    subst hi
    exact .unary opn dn sn ho (gp_of_allocOp hd hsp.1) (gp_of_allocOp hs hsp.2)

/-! ## Loads and stores -/

/-- The register-indexed addresses the lowering legalises: a base and an index that are
    allocated names, at a stride x86 encodes. -/
def SibOk (F W Q : Nat) : LOperand → Prop
  | .arrIdx b x sc => AllocOp F W Q (.reg b) ∧ AllocOp F W Q (.reg x) ∧ x86SibScale sc = true
  | _ => False

/-- The prelude of `legalizeSibElem` has legal forms, and its address has general-purpose
    base and index, the index the scratch `R15` or the index of the address. -/
theorem legalizeSibElem_legal {b x : String} {sc : Nat} (hb : AllocOp F W Q (.reg b))
    (hx : AllocOp F W Q (.reg x)) :
    (∀ i ∈ (legalizeSibElem (.arrIdx b x sc)).1, LF F W Q i) ∧
      ∃ b' x', (legalizeSibElem (.arrIdx b x sc)).2 = .arrIdx b' x' sc ∧ isGpName b' = true ∧
        isGpName x' = true ∧ (x' = reloadScratch ∨ x' = x) := by
  have hm : isMovMnem "MOV:64" = true := by decide +kernel
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [legalizeSibElem, List.mem_append] at hi
    rcases hi with hi | hi <;> split_ifs at hi <;>
      simp only [List.mem_singleton, List.not_mem_nil] at hi
    · subst hi
      exact lf_mov_left hm isGpName_reloadScratch2 hb
    · subst hi
      exact lf_mov_left hm isGpName_reloadScratch hx
  · simp only [legalizeSibElem]
    refine ⟨_, _, rfl, ?_, ?_, ?_⟩
    · split_ifs with h
      · exact isGpName_reloadScratch2
      · exact gp_of_allocOp hb (by simpa [LOperand.isSpill, sibNameSpill] using h)
    · split_ifs with h
      · exact isGpName_reloadScratch
      · exact gp_of_allocOp hx (by simpa [LOperand.isSpill, sibNameSpill] using h)
    · split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- The memref base reload has legal forms when every save slot it reads resolves, and keeps
    a register-indexed address of allocated names one. -/
theorem reloadMemrefBase_legal (mbr : String → Option String) (o : LOperand)
    (hq : ∀ b q, mbr b = some q → OpResolves F W Q q) :
    (∀ i ∈ (reloadMemrefBase mbr o).1, LF F W Q i) ∧
      (SibOk F W Q o → SibOk F W Q (reloadMemrefBase mbr o).2) ∧
      (∀ n, o = .reg n → (reloadMemrefBase mbr o).2 = o) := by
  cases o with
  | arrIdx b x sc =>
    cases hb : mbr b with
    | none =>
      simp only [reloadMemrefBase, hb]
      exact ⟨by simp, id, fun _ h => by cases h⟩
    | some q =>
      simp only [reloadMemrefBase, hb]
      refine ⟨?_, fun ⟨_, hx, hsc⟩ => ⟨allocOp_of_gp isGpName_reloadScratch2, hx, hsc⟩,
        fun _ h => by cases h⟩
      intro i hi
      simp only [List.mem_singleton] at hi
      subst hi
      exact lf_mov_res_left (by decide +kernel) isGpName_reloadScratch2 (hq b q hb)
  | _ => exact ⟨by simp [reloadMemrefBase], fun h => by simpa [reloadMemrefBase] using h,
      fun _ _ => rfl⟩

/-- The source of a load the lowering legalises: a resolving name under a load of
    `x86MemMov`, or a register-indexed address of allocated names under `LOADIDX`. -/
def LoadSrc (F W Q : Nat) (opn : String) (o : LOperand) : Prop :=
  (∃ n, o = .reg n ∧ OpResolves F W Q n ∧ x86MemMov opn = true) ∨
    (SibOk F W Q o ∧ stripWidthTag opn = "LOADIDX")

/-- **The load legalisation has legal forms**: on an allocated destination and a source of
    `LoadSrc`, every instruction of `legalizeMemLoad` has a legal form. -/
theorem legalizeMemLoad_legal {dst src : LOperand} {opn mov : String}
    (hm : isMovMnem mov = true) (hd : AllocOp F W Q dst) (hs : LoadSrc F W Q opn src) :
    ∀ i ∈ legalizeMemLoad dst src opn mov, LF F W Q i := by
  have h15 := isGpName_reloadScratch
  obtain ⟨dn, rfl, hd'⟩ := hd
  have hd : AllocOp F W Q (.reg dn) := ⟨dn, rfl, hd'⟩
  have hsm : ∀ sc, isMovMnem (if sc ≥ 8 then "MOV:64" else mov) = true := by
    intro sc
    split_ifs
    · decide +kernel
    · exact hm
  -- the register written by the load: `R15` for a spilled destination, the destination
  -- otherwise
  have hw : ∀ (P : String → Prop), P reloadScratch → ((LOperand.reg dn).isSpill = false →
      P dn) → ∀ r, (r = reloadScratch ∨ ((LOperand.reg dn).isSpill = false ∧ r = dn)) →
      P r := by
    rintro P h1 h2 r (rfl | ⟨h, rfl⟩)
    · exact h1
    · exact h2 h
  intro i hi
  rcases hs with ⟨n, rfl, hn, ho⟩ | ⟨hsib, ho⟩
  · simp only [legalizeMemLoad, legalizeSibElem, List.nil_append] at hi
    split_ifs at hi with hsp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact .memMov opn _ n ho (Or.inl h15) hn (by simp [x86Enc, encMemName_of_isGpName h15])
      · exact lf_mov_right hm h15 hd
    · simp only [List.mem_singleton] at hi
      subst hi
      have hg := gp_of_allocOp hd (by simpa using hsp)
      exact .memMov opn _ n ho (Or.inl hg) hn (by simp [x86Enc, encMemName_of_isGpName hg])
  · cases src with
    | reg _ => exact hsib.elim
    | arr _ _ => exact hsib.elim
    | imm _ => exact hsib.elim
    | arrIdx b x sc =>
    obtain ⟨hb, hx, hsc⟩ := hsib
    obtain ⟨hpre, b', x', hfix, hb', hx', -⟩ := legalizeSibElem_legal (sc := sc) hb hx
    have hl : x86SibLoad opn x' sc = true := by simp [x86SibLoad, hsc, ho]
    rcases hp : legalizeSibElem (.arrIdx b x sc) with ⟨pre, s'⟩
    rw [hp] at hpre hfix
    simp only at hpre hfix
    subst hfix
    unfold legalizeMemLoad at hi
    rw [hp] at hi
    dsimp only at hi
    generalize hsmv : (if sc ≥ 8 then "MOV:64" else mov) = smov at hi
    have hsm' : isMovMnem smov = true := hsmv ▸ hsm sc
    simp only [List.mem_append] at hi
    rcases hi with hi | hi
    · exact hpre i hi
    · split_ifs at hi with hsp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact .sibLoad opn _ b' x' sc hl h15 hb' hx'
        · exact lf_mov_right hsm' h15 hd
      · simp only [List.mem_singleton] at hi
        subst hi
        exact .sibLoad opn dn b' x' sc hl (gp_of_allocOp hd (by simpa using hsp)) hb' hx'

/-- **The store legalisation has legal forms**: on a register-indexed address of allocated
    names (`SibOk`), an allocated value and the store `STOREIDX`, every instruction of
    `legalizeMemStoreK` has a legal form, for every index constant and array destination. -/
theorem legalizeMemStoreK_legal (k : Option Nat) (dArr : LOperand) {addr val : LOperand}
    {opn mov : String} (hm : isMovMnem mov = true) (hst : stripWidthTag opn = "STOREIDX")
    (ha : SibOk F W Q addr) (hv : AllocOp F W Q val) :
    ∀ i ∈ legalizeMemStoreK k dArr addr val opn mov, LF F W Q i := by
  have h15 := isGpName_reloadScratch
  have h14 := isGpName_reloadScratch2
  have hm64 : isMovMnem "MOV:64" = true := by decide +kernel
  cases addr with
  | reg _ => exact ha.elim
  | arr _ _ => exact ha.elim
  | imm _ => exact ha.elim
  | arrIdx b x sc =>
  obtain ⟨hb, hx, hsc⟩ := ha
  obtain ⟨vn, rfl, hv'⟩ := hv
  have hv : AllocOp F W Q (.reg vn) := ⟨vn, rfl, hv'⟩
  intro i hi
  unfold legalizeMemStoreK at hi
  split at hi
  · next l hl =>
    have hres : ∀ b' c, isGpName b' = true →
        LF F W Q (.Lopn [.reg (memName b' (8 * c))] "STORE:64" [.reg reloadScratch]) :=
      fun b' c hb' => .memMov _ _ _ (by decide +kernel) (opResolves_memName hb' _) (Or.inl h15)
        (by simp [x86Enc, encMemName_of_isGpName h15])
    unfold constIdxStore? at hl
    dsimp only at hl
    by_cases hbs : sibNameSpill b = true
    · simp only [hbs, if_true] at hl
      split_ifs at hl with h1
      split at hl
      · next c =>
        split_ifs at hl with h2
        cases hl
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · exact lf_mov_left hm64 h14 hb
        · exact lf_mov_left hm64 h15 hv
        · exact hres _ c h14
      · cases hl
    · have hbs' : (LOperand.reg b).isSpill = false := by
        simpa [LOperand.isSpill, sibNameSpill] using hbs
      rw [Bool.not_eq_true] at hbs
      simp only [hbs, Bool.false_eq_true, if_false] at hl
      split_ifs at hl with h1
      split at hl
      · next c =>
        split_ifs at hl with h2
        cases hl
        simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact lf_mov_left hm64 h15 hv
        · exact hres _ c (gp_of_allocOp hb hbs')
      · cases hl
  · obtain ⟨hpre, b', x', hfix, hb', hx', hxx⟩ := legalizeSibElem_legal (sc := sc) hb hx
    have hsto : ∀ r, isGpName r = true →
        LF F W Q (.Lopn [dArr] opn [.arrIdx b' x' sc, .reg r]) := fun r hr =>
      .sibStore dArr opn b' x' r sc (show x86SibStore opn sc = true by
        simp [x86SibStore, hst, hsc]) hb' hx' hr
    have hrm : isMovMnem (if sc ≥ 8 then "MOV:64" else mov) = true := by
      split_ifs
      · exact hm64
      · exact hm
    rcases hp : legalizeSibElem (.arrIdx b x sc) with ⟨pre, a'⟩
    rw [hp] at hpre hfix
    simp only at hpre hfix
    subst hfix
    unfold legalizeMemStore at hi
    rw [hp] at hi
    dsimp only at hi
    generalize hrmv : (if sc ≥ 8 then "MOV:64" else mov) = rmov at hi
    have hrm : isMovMnem rmov = true := hrmv ▸ hrm
    have hmem : OpResolves F W Q ("mem." ++ reloadScratch2 ++ ".0") :=
      Or.inr (Or.inr (by decide +kernel))
    cases hvs : (LOperand.reg vn).isSpill
    · simp only [hvs, List.mem_append, List.mem_singleton] at hi
      rcases hi with hi | rfl
      · exact hpre i hi
      · exact hsto vn (gp_of_allocOp hv hvs)
    · simp only [hvs] at hi
      split_ifs at hi with hxe
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with hi | rfl | rfl | rfl
        · exact hpre i hi
        · simp only [beq_iff_eq] at hxe
          subst hxe
          exact .sibLoad _ _ _ _ sc (show x86SibLoad "LEA:64" reloadScratch sc = true by
            simp [x86SibLoad, hsc]; decide +kernel) h14 hb' hx'
        · exact lf_mov_left hrm h15 hv
        · exact lf_mov_res_right hrm h15 hmem
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with hi | rfl | rfl
        · exact hpre i hi
        · exact lf_mov_left hrm h15 hv
        · exact hsto _ h15

/-! ## One-source instructions and the spill legalisation -/

/-- **The one-source legalisation has legal forms**: on a register copy (`MOV`, `MOV:64`,
    `MOVQ`) into an allocated operand from a source a move may copy under the move
    selection, and on any other mnemonic when the single instruction has a legal form. -/
theorem legalizeOneSrc_legal (u64 : Bool) {opn : String} {d s : LOperand}
    (hmov : (stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ") = true →
      isMovMnem opn = true ∧ AllocOp F W Q d ∧ ValOk F W Q (spillImmMovMnem u64 opn d s) s)
    (hone : (stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ") = false →
      LF F W Q (.Lopn [d] opn [s])) :
    ∀ i ∈ legalizeOneSrc u64 opn d s, LF F W Q i := by
  intro i hi
  unfold legalizeOneSrc at hi
  split_ifs at hi with h
  · obtain ⟨hm, hd, hs⟩ := hmov h
    have hm' : isMovMnem (spillImmMovMnem u64 opn d s) = true := by
      unfold spillImmMovMnem
      split
      · split_ifs
        · decide +kernel
        · exact hm
      · exact hm
    exact legalizeMov_legal hm' hd hs i hi
  · simp only [Bool.not_eq_true] at h
    have he : spillImmMovMnem u64 opn d s = opn := by
      apply spillImmMovMnem_of_ne
      intro he
      subst he
      revert h
      decide +kernel
    simp only [he, List.mem_singleton] at hi
    subst hi
    exact hone h

/-- The hypotheses of the arm `legalizeSpillDst`: a select `CMOV:64` with a spilled
    destination or condition has allocated destination and condition and selected values in
    general-purpose registers; a comparison of `isSetccMnem` with a spilled operand is one the
    encoder builds, over allocated operands; and when neither legalisation applies, the
    single instruction has a legal form. -/
structure SpillDstOk (F W Q : Nat) (dsts : List LOperand) (opn : String)
    (srcs : List LOperand) : Prop where
  /-- The scratch select. -/
  sel : ∀ l, cmovSpillDst? dsts opn srcs = some l → ∀ d c t f, dsts = [d] → srcs = [c, t, f] →
    AllocOp F W Q d ∧ AllocOp F W Q c ∧
      ∃ tn fn, t = .reg tn ∧ f = .reg fn ∧ isGpName tn = true ∧ isGpName fn = true
  /-- The scratch comparison. -/
  cmp : ∀ l, setccSpill? dsts opn srcs = some l → isSetccEncMnem opn = true ∧
    (∀ o ∈ dsts, AllocOp F W Q o) ∧ ∀ o ∈ srcs, AllocOp F W Q o
  /-- The single instruction. -/
  one : cmovSpillDst? dsts opn srcs = none → setccSpill? dsts opn srcs = none →
    LF F W Q (.Lopn dsts opn srcs)

/-- **The spill legalisation of a general instruction has legal forms** under `SpillDstOk`. -/
theorem legalizeSpillDst_legal {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    (h : SpillDstOk F W Q dsts opn srcs) :
    ∀ i ∈ legalizeSpillDst dsts opn srcs, LF F W Q i := by
  intro i hi
  unfold legalizeSpillDst at hi
  split at hi
  · next l hl =>
    have hl' := hl
    unfold cmovSpillDst? at hl'
    split at hl'
    · next d c t f =>
      split_ifs at hl' with hb
      cases hl'
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨hd, hc, tn, fn, rfl, rfl, ht, hf⟩ := h.sel _ hl d c t f rfl rfl
      rw [hb.2] at hi
      exact x86Enc_complete.cmovSpillSeqI_legal (c := (F, W, Q)) x86Isa_selectMnemonic
        (allocOp_iff_allocOpI.1 hd) (allocOp_iff_allocOpI.1 hc) ht hf i hi
    · cases hl'
  · next hc =>
    split at hi
    · next l hl =>
      obtain ⟨ho, hd, hs⟩ := h.cmp l hl
      exact x86Enc_complete.setccSpillI?_legal (c := (F, W, Q)) hl ho
        (fun o ho => allocOp_iff_allocOpI.1 (hd o ho)) (fun o ho => allocOp_iff_allocOpI.1 (hs o ho))
        i hi
    · next hs =>
      simp only [List.mem_singleton] at hi
      subst hi
      exact h.one hc hs


/-! ## One position of `physPositionEmit` -/

/-- The move mnemonic of the lowering at an operation mnemonic: `MOV:64` for a `:64`-tagged
    mnemonic, `MOV` otherwise. -/
def movFor (opn : String) : String := if hasSuffix opn ":64" then "MOV:64" else "MOV"

theorem isMovMnem_movFor (opn : String) : isMovMnem (movFor opn) = true := by
  unfold movFor
  split <;> decide +kernel

/-- The shifts of the two-address binops, `SHL` and `SHR`. -/
def isShiftMnem (opn : String) : Bool := stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR"

/-- The shift count the lowering reads from the second source of a binop: an immediate, or
    the constant the oracle gives for a register. -/
def shiftCount (shiftImm : ShiftImmOracle) : LOperand → Option Nat
  | .imm v => some v
  | .reg n => shiftImm n
  | _ => none

/-- **The hypotheses of one position** on the virtual instruction `x`, the operand map `rm`
    and the shift oracle, one field per arm of the expansion of `physPositionEmit`:

    * `binop`: a two-address binop has an allocated destination, a first source a move may
      copy, and a second source that is allocated or an immediate; a shift by a register
      (no constant count) is a three-register shift of `x86ShiftReg`;
    * `store`: a memory store is a `STOREIDX` at a register-indexed address of allocated
      names (`SibOk`) of an allocated value;
    * `pair`, `multi`: every other instruction of two or more sources satisfies the
      hypotheses of `legalizeSpillDst` (`SpillDstOk`);
    * `native`: a native shift has allocated operands and is a one-source operation of
      `x86Unary`;
    * `load`: a memory load has an allocated destination and a source of `LoadSrc`;
    * `oneSrc`: a one-source register copy is a move mnemonic into an allocated destination
      from a source a move may copy, and any other one-source instruction has a legal form
      after the remapping;
    * `rest`, `ctrl`: an instruction of any other shape has a legal form after the remapping.

    The arms `pair`, `multi` (when no scratch legalisation applies), `oneSrc` (off the
    copies), `rest` and `ctrl` emit the remapped instruction unchanged. -/
structure PosOk (F W Q : Nat) (rm : LOperand → LOperand) (shiftImm : ShiftImmOracle)
    (x : LinstrR) : Prop where
  /-- The two-address binops. -/
  binop : ∀ d tl opn s0 s1 tl1, x = .Lopn (d :: tl) opn (s0 :: s1 :: tl1) →
    isTwoAddrBinop opn = true →
    AllocOp F W Q (rm d) ∧ ValOk F W Q (movFor opn) (rm s0) ∧
      (AllocOp F W Q (rm s1) ∨ ∃ v, rm s1 = .imm v) ∧
      (isShiftMnem opn = true → shiftCount shiftImm s1 = none → x86ShiftReg opn = true)
  /-- The memory stores. -/
  store : ∀ d opn addr val, x = .Lopn [d] opn [addr, val] → isTwoAddrBinop opn = false →
    isMemStore opn = true →
    stripWidthTag opn = "STOREIDX" ∧ SibOk F W Q (rm addr) ∧ AllocOp F W Q (rm val)
  /-- The other instructions of one destination and two sources. -/
  pair : ∀ d opn addr val, x = .Lopn [d] opn [addr, val] → isTwoAddrBinop opn = false →
    isMemStore opn = false → SpillDstOk F W Q [rm d] opn [rm addr, rm val]
  /-- The other instructions of a destination and two or more sources. -/
  multi : ∀ d tl opn s0 s1 tl1, x = .Lopn (d :: tl) opn (s0 :: s1 :: tl1) →
    isTwoAddrBinop opn = false →
    (∀ d' a v, d :: tl = [d'] → s0 :: s1 :: tl1 = [a, v] → False) →
    SpillDstOk F W Q ((d :: tl).map rm) opn ((s0 :: s1 :: tl1).map rm)
  /-- The native shifts. -/
  native : ∀ d opn s, x = .Lopn [d] opn [s] → isNativeShiftRotate opn = true →
    AllocOp F W Q (rm d) ∧ AllocOp F W Q (rm s) ∧ x86Unary opn = true
  /-- The memory loads. -/
  load : ∀ d opn s, x = .Lopn [d] opn [s] → isNativeShiftRotate opn = false →
    isMemLoad opn = true → AllocOp F W Q (rm d) ∧ LoadSrc F W Q opn (rm s)
  /-- The other one-source instructions. -/
  oneSrc : ∀ d opn s, x = .Lopn [d] opn [s] → isNativeShiftRotate opn = false →
    isMemLoad opn = false →
    ((stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ") = true →
      isMovMnem opn = true ∧ AllocOp F W Q (rm d) ∧ ValOk F W Q opn (rm s)) ∧
    ((stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ") = false →
      LF F W Q (.Lopn [rm d] opn [rm s]))
  /-- The instructions of any other shape. -/
  rest : ∀ dsts opn srcs, x = .Lopn dsts opn srcs →
    (∀ d tl s0 s1 tl1, dsts = d :: tl → srcs = s0 :: s1 :: tl1 → False) →
    (∀ d s, dsts = [d] → srcs = [s] → False) →
    LF F W Q (.Lopn (dsts.map rm) opn (srcs.map rm))
  /-- The instructions other than an operation. -/
  ctrl : (∀ dsts opn srcs, x ≠ .Lopn dsts opn srcs) → LF F W Q x

/-- A move selection of `spillImmMovMnem` keeps a source a move may copy. -/
theorem valOk_spillImmMovMnem {u64 : Bool} {opn : String} {d s : LOperand}
    (h : ValOk F W Q opn s) : ValOk F W Q (spillImmMovMnem u64 opn d s) s := by
  rcases h with h | ⟨v, rfl, hv⟩
  · exact Or.inl h
  · refine Or.inr ⟨v, rfl, ?_⟩
    unfold spillImmMovMnem
    dsimp only
    split_ifs with hc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp [x86SlotImm, hc.2]
    · exact hv

/-- A two-address binop other than a shift is an operation of `x86Alu`. -/
theorem x86Alu_of_binop {opn : String} (hb : isTwoAddrBinop opn = true)
    (hs : isShiftMnem opn = false) : x86Alu opn = true := by
  simp only [isTwoAddrBinop, List.contains_iff_mem, List.mem_cons, List.not_mem_nil,
    or_false] at hb
  simp only [isShiftMnem, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hs
  simp only [x86Alu, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false]
  rcases hb with h | h | h | h | h | h | h | h
  all_goals first | exact absurd h hs.1 | exact absurd h hs.2 | simp [h]

/-- A two-address binop that is a shift has an immediate form at every count. -/
theorem x86AluImm_of_shift {opn : String} (hs : isShiftMnem opn = true) (v : Nat) :
    x86AluImm opn v = true := by
  simp only [isShiftMnem, Bool.or_eq_true, beq_iff_eq] at hs
  rcases hs with hs | hs <;> simp [x86AluImm, hs]

/-- An immediate of a two-address binop that is below `2^31` under the move `MOV:64` of the
    lowering fits the `imm32` field at the width of the binop. -/
theorem imm32Fits_of_movFor {opn : String} {v : Nat} (hb : isTwoAddrBinop opn = true)
    (hv : movFor opn = "MOV:64" → v < 2 ^ 31) : imm32Fits (rexW (mnemWidth opn)) v = true := by
  have hq : opn ≠ "MOVQ" := by
    rintro rfl
    revert hb
    decide +kernel
  unfold movFor at hv
  unfold imm32Fits rexW mnemWidth
  by_cases h : hasSuffix opn ":64" = true
  · have hlt := hv (by simp [h])
    simp only [h]
    simp
    omega
  · simp only [h, if_false, Bool.false_or, decide_eq_true_eq, hq]
    split_ifs <;> first | omega | simp

/-- The binding index of a position: the number of operations before it. -/
def posBidx (body : Lcmd) (virtIdx : Nat) : Nat :=
  ((body.take virtIdx).filter (fun li =>
    match li.li_i with | .Lopn _ _ _ => true | _ => false)).length

/-- **Every instruction of one position of `physPositionEmit` has a legal form** at the x86
    encoder `x86Enc` in the context `(F, W, Q)`, over operands the allocation resolves. Let
    `rm` be the operand map of `physPositionEmit`. Suppose the ABI moves are register moves
    (`abiW` is none of the narrow widths `8`, `16` and the vector width `256`, whose moves
    `MOV:8`, `MOV:16`, `VMOVDQU` the encoder does not build); the argument registers are
    allocated (`hargs`); the save slots the argument loads, the memref base reload and the
    output store read resolve (`hsave`, `hmbr`, `hrdi`); the input and output bases are
    general-purpose registers (`hloadBase`, `hstoreBase`); the post-call reloads move
    resolving save slots into general-purpose registers (`hcall`); the destination of a
    stored binding is allocated (`hout`); and the virtual instruction satisfies `PosOk`. -/
theorem lower_legal (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String) (outStoreMap : OutStoreMap)
    (storeBase : String) (abiW : Nat) (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat)
    (i : Linstr) (virtIdx : Nat) (rm : LOperand → LOperand)
    (hrm : rm =
      let tbl := straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
      if bodyHasCall body then remapOperandCalleeSave body tbl else remapOperand body tbl)
    (habi : abiW ≠ 8 ∧ abiW ≠ 16 ∧ abiW ≠ 256)
    (hargs : ∀ s, AllocOp F W Q (.reg (physNameForBody body
      (straightCallComposeTable body (physTableOut body outStoreMap reservedVec))
      (argName s))))
    (hsave : ∀ base, OpResolves F W Q (abiLoadSave base))
    (hrdi : OpResolves F W Q abiSaveRdiName)
    (hmbr : ∀ b q, memrefBaseReload b = some q → OpResolves F W Q q)
    (hloadBase : isGpName loadBase = true) (hstoreBase : isGpName storeBase = true)
    (hcall : ∀ p ∈ callArgBaseReload, isGpName p.1 = true ∧ OpResolves F W Q p.2)
    (hout : ∀ d tl opn srcs, i.li_i = .Lopn (d :: tl) opn srcs →
      numBindings body - outStoreMap.length ≤ posBidx body virtIdx →
      posBidx body virtIdx < numBindings body → AllocOp F W Q (rm d))
    (hpos : PosOk F W Q rm shiftImm i.li_i) :
    ∀ r ∈ physPositionEmit shiftImm body inLoadMap loadBase outStoreMap storeBase abiW
      memrefBaseReload callArgBaseReload reservedVec (i, virtIdx), LF F W Q r.li_i := by
  intro r hr
  obtain ⟨ii, x⟩ := i
  simp only at hout hpos
  obtain ⟨h8, h16, h256⟩ := habi
  have hb8 : (abiW == 8) = false := by simpa using h8
  have hb16 : (abiW == 16) = false := by simpa using h16
  have hb256 : (abiW == 256) = false := by simpa using h256
  have hmovB : ∀ b : Bool, isMovMnem (if b = true then "MOV:64" else "MOV") = true := by
    intro b
    cases b <;> decide +kernel
  have h15 := isGpName_reloadScratch
  have h14 := isGpName_reloadScratch2
  have hmq : isMovMnem "MOVQ" = true := by decide +kernel
  unfold physPositionEmit at hr
  simp only [List.mem_append, ← hrm, hb8, hb16, hb256, Bool.false_eq_true, if_false] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · -- the inline argument loads
    rw [List.mem_flatMap] at hr
    obtain ⟨⟨s, base, off⟩, -, hr⟩ := hr
    split at hr <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl | rfl
    all_goals first
      | exact lf_mov_res_left hmq h14 (hsave base)
      | exact lf_mov_res_left (hmovB _) h15 (opResolves_memName hloadBase off)
      | exact lf_mov_right (hmovB _) h15 (hargs s)
      | skip
    · rename_i hsp
      exact .mov _ _ _ (hmovB _) (allocOp_iff_allocOpI.1 (hargs s) |> x86Enc_complete.allocOp_resolves)
        (opResolves_memName hloadBase off) (by
          have := (allocOp_iff_allocOpI.1 (hargs s) |> x86Enc_complete.allocOp_memName)
          change encMemName _ = _ at this
          simp [x86Enc, this, hsp])
  · -- the expansion
    have hwrap : ∀ (L : List LinstrR) (r : Linstr),
        r ∈ L.map (fun r => ({ li_ii := ii, li_i := r } : Linstr)) → r.li_i ∈ L := by
      intro L r h
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      exact ha
    split at hr
    · next d tail opn s0 s1 tail1 =>
      split at hr
      · next hbin =>
        obtain ⟨hd, h0, h1, hsh⟩ := hpos.binop d tail opn s0 s1 tail1 rfl hbin
        split at hr
        · next v hv =>
          refine lowerTwoAddrShiftImm_legal (isMovMnem_movFor opn) hd h0 ?_ _ (hwrap _ _ hr)
          split_ifs at hv with hs
          exact x86AluImm_of_shift hs v
        · next hv =>
          refine lowerTwoAddr_legal (isMovMnem_movFor opn) hd h0 h1 ?_ ?_ _ (hwrap _ _ hr)
          · cases hs : isShiftMnem opn
            · exact Or.inl (x86Alu_of_binop hbin hs)
            · refine Or.inr (hsh hs ?_)
              have hs' : (stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR") = true := hs
              simp only [hs', if_true] at hv
              cases s1 <;> simp_all [shiftCount]
          · intro v _ hlt
            cases hs : isShiftMnem opn
            · simp [x86AluImm, x86Alu_of_binop hbin hs, imm32Fits_of_movFor hbin hlt]
            · exact x86AluImm_of_shift hs v
      · next hbin =>
        split at hr
        · next _ d' opn' addr val heq =>
          simp only [LinstrR.Lopn.injEq, List.cons.injEq] at heq
          obtain ⟨⟨h1, rfl⟩, h2, h3, h4, rfl⟩ := heq
          subst h1 h2 h3 h4
          split at hr
          · next hst =>
            obtain ⟨hsto, hA, hv⟩ := hpos.store d opn s0 s1 rfl (by simpa using hbin) hst
            obtain ⟨hpre, hA', -⟩ := reloadMemrefBase_legal memrefBaseReload (rm s0) hmbr
            rw [List.mem_append] at hr
            rcases hr with hr | hr
            · exact hpre _ (hwrap _ _ hr)
            · exact legalizeMemStoreK_legal _ _ (isMovMnem_movFor opn) hsto (hA' hA) hv _
                (hwrap _ _ hr)
          · next hst =>
            exact legalizeSpillDst_legal (hpos.pair d opn s0 s1 rfl (by simpa using hbin)
              (by simpa using hst)) _ (hwrap _ _ hr)
        · next _ dsts opn' srcs hne heq =>
          simp only [LinstrR.Lopn.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact legalizeSpillDst_legal (hpos.multi d tail opn s0 s1 tail1 rfl
            (by simpa using hbin) hne) _ (hwrap _ _ hr)
        · next _ _ hne => exact (hne _ _ _ rfl).elim
    · next _ d opn s =>
      split at hr
      · next hnat =>
        obtain ⟨hd, hs, hu⟩ := hpos.native d opn s rfl hnat
        exact lowerNativeShiftRotate_legal (isMovMnem_movFor opn) hd hs hu _ (hwrap _ _ hr)
      · next hnat =>
        split at hr
        · next hld =>
          obtain ⟨hd, hs⟩ := hpos.load d opn s rfl (by simpa using hnat) hld
          obtain ⟨hpre, hsib, hregEq⟩ := reloadMemrefBase_legal memrefBaseReload (rm s) hmbr
          have hs' : LoadSrc F W Q opn (reloadMemrefBase memrefBaseReload (rm s)).2 := by
            rcases hs with ⟨n, hn, hres, hm⟩ | ⟨hsb, hl⟩
            · exact Or.inl ⟨n, by rw [hregEq n hn, hn], hres, hm⟩
            · exact Or.inr ⟨hsib hsb, hl⟩
          rw [List.mem_append] at hr
          rcases hr with hr | hr
          · exact hpre _ (hwrap _ _ hr)
          · exact legalizeMemLoad_legal (isMovMnem_movFor opn) hd hs' _ (hwrap _ _ hr)
        · next hld =>
          obtain ⟨hmov, hone⟩ := hpos.oneSrc d opn s rfl (by simpa using hnat) (by simpa using hld)
          refine legalizeOneSrc_legal _ (fun h => ?_) hone _ (hwrap _ _ hr)
          obtain ⟨hm, hd, hs⟩ := hmov h
          exact ⟨hm, hd, valOk_spillImmMovMnem hs⟩
    · next _ dsts opn srcs h1 h2 =>
      simp only [List.mem_singleton] at hr
      subst hr
      exact hpos.rest dsts opn srcs rfl h1 h2
    · next _ _ _ hne =>
      simp only [List.mem_singleton] at hr
      subst hr
      exact hpos.ctrl (fun dsts opn srcs h => hne dsts opn srcs h)
  · -- the pointer reloads after a call
    split at hr
    · rw [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      exact lf_mov_res_left hmq (hcall p hp).1 (hcall p hp).2
    · simp at hr
  · -- the inline output store
    split at hr
    · next d tail opn srcs =>
      split at hr
      · next hg =>
        obtain ⟨n, hn, hn'⟩ := hout d tail opn srcs rfl hg.1 hg.2
        have hdn : AllocOp F W Q (.reg n) := ⟨n, rfl, hn'⟩
        rw [hn] at hr
        split at hr
        · next off _ =>
          split at hr <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          · rcases hr with rfl | rfl | rfl
            · exact lf_mov_left (hmovB _) h15 hdn
            · exact lf_mov_res_left hmq h14 hrdi
            · exact lf_mov_res_right (hmovB _) h15 (opResolves_memName hstoreBase off)
          · next hsp =>
            rcases hr with rfl | rfl
            · exact lf_mov_res_left hmq h14 hrdi
            · have hg' := gp_of_allocOp hdn (by simpa using hsp)
              exact lf_mov_res_right (hmovB _) hg' (opResolves_memName hstoreBase off)
        · simp at hr
      · simp at hr
    · simp at hr


/-! ## The stored body and load forwarding -/

/-- **Every instruction of `physBodyWithStores` has a legal form** at the x86 encoder in the
    context `(F, W, Q)`, under the hypotheses of `lower_legal` at every position. -/
theorem physBodyWithStores_legal (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String) (outStoreMap : OutStoreMap)
    (storeBase : String) (abiW : Nat) (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat)
    (rm : LOperand → LOperand)
    (hrm : rm =
      let tbl := straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
      if bodyHasCall body then remapOperandCalleeSave body tbl else remapOperand body tbl)
    (habi : abiW ≠ 8 ∧ abiW ≠ 16 ∧ abiW ≠ 256)
    (hargs : ∀ s, AllocOp F W Q (.reg (physNameForBody body
      (straightCallComposeTable body (physTableOut body outStoreMap reservedVec))
      (argName s))))
    (hsave : ∀ base, OpResolves F W Q (abiLoadSave base))
    (hrdi : OpResolves F W Q abiSaveRdiName)
    (hmbr : ∀ b q, memrefBaseReload b = some q → OpResolves F W Q q)
    (hloadBase : isGpName loadBase = true) (hstoreBase : isGpName storeBase = true)
    (hcall : ∀ p ∈ callArgBaseReload, isGpName p.1 = true ∧ OpResolves F W Q p.2)
    (hout : ∀ p ∈ body.zipIdx, ∀ d tl opn srcs, p.1.li_i = .Lopn (d :: tl) opn srcs →
      numBindings body - outStoreMap.length ≤ posBidx body p.2 →
      posBidx body p.2 < numBindings body → AllocOp F W Q (rm d))
    (hpos : ∀ p ∈ body.zipIdx, PosOk F W Q rm shiftImm p.1.li_i) :
    ∀ r ∈ physBodyWithStores shiftImm body inLoadMap loadBase outStoreMap storeBase abiW
      memrefBaseReload callArgBaseReload reservedVec, LF F W Q r.li_i := by
  intro r hr
  rw [physBodyWithStores_eq_flatMap, List.mem_flatMap] at hr
  obtain ⟨⟨i, virtIdx⟩, hp, hr⟩ := hr
  exact lower_legal shiftImm body inLoadMap loadBase outStoreMap storeBase abiW
    memrefBaseReload callArgBaseReload reservedVec i virtIdx rm hrm habi hargs hsave hrdi hmbr
    hloadBase hstoreBase hcall (hout _ hp) (hpos _ hp) r hr

/-- **Load forwarding preserves the legal forms of the lowering**: under the hypotheses of
    `physBodyWithStores_legal`, every instruction of `loadCSE` of `physBodyWithStores` has a
    legal form at the x86 encoder in the context `(F, W, Q)`. -/
theorem lower_legal_loadCSE (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String) (outStoreMap : OutStoreMap)
    (storeBase : String) (abiW : Nat) (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat)
    (rm : LOperand → LOperand)
    (hrm : rm =
      let tbl := straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
      if bodyHasCall body then remapOperandCalleeSave body tbl else remapOperand body tbl)
    (habi : abiW ≠ 8 ∧ abiW ≠ 16 ∧ abiW ≠ 256)
    (hargs : ∀ s, AllocOp F W Q (.reg (physNameForBody body
      (straightCallComposeTable body (physTableOut body outStoreMap reservedVec))
      (argName s))))
    (hsave : ∀ base, OpResolves F W Q (abiLoadSave base))
    (hrdi : OpResolves F W Q abiSaveRdiName)
    (hmbr : ∀ b q, memrefBaseReload b = some q → OpResolves F W Q q)
    (hloadBase : isGpName loadBase = true) (hstoreBase : isGpName storeBase = true)
    (hcall : ∀ p ∈ callArgBaseReload, isGpName p.1 = true ∧ OpResolves F W Q p.2)
    (hout : ∀ p ∈ body.zipIdx, ∀ d tl opn srcs, p.1.li_i = .Lopn (d :: tl) opn srcs →
      numBindings body - outStoreMap.length ≤ posBidx body p.2 →
      posBidx body p.2 < numBindings body → AllocOp F W Q (rm d))
    (hpos : ∀ p ∈ body.zipIdx, PosOk F W Q rm shiftImm p.1.li_i) :
    ∀ r ∈ CatCrypt.Crypto.Optimizer.LoadCSE.loadCSE (physBodyWithStores shiftImm body
      inLoadMap loadBase outStoreMap storeBase abiW memrefBaseReload callArgBaseReload
      reservedVec), LF F W Q r.li_i :=
  x86Enc_complete.loadCSE_legalI (c := (F, W, Q)) _
    (physBodyWithStores_legal shiftImm body inLoadMap loadBase outStoreMap storeBase abiW
      memrefBaseReload callArgBaseReload reservedVec rm hrm habi hargs hsave hrdi hmbr hloadBase
      hstoreBase hcall hout hpos)

/-- **The forwarded stored body is encodable**: under the hypotheses of `lower_legal_loadCSE`
    at the context of the forwarded body under the x86 encoder, `loadCSE` of
    `physBodyWithStores` is accepted by `encodableLcmd`. -/
theorem encodable_loadCSE_physBodyWithStores (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String) (outStoreMap : OutStoreMap)
    (storeBase : String) (abiW : Nat) (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat)
    (rm : LOperand → LOperand)
    (hctx : (F, W, Q) = x86Enc.ctx (CatCrypt.Crypto.Optimizer.LoadCSE.loadCSE
      (physBodyWithStores shiftImm body inLoadMap loadBase outStoreMap storeBase abiW
        memrefBaseReload callArgBaseReload reservedVec)))
    (hrm : rm =
      let tbl := straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
      if bodyHasCall body then remapOperandCalleeSave body tbl else remapOperand body tbl)
    (habi : abiW ≠ 8 ∧ abiW ≠ 16 ∧ abiW ≠ 256)
    (hargs : ∀ s, AllocOp F W Q (.reg (physNameForBody body
      (straightCallComposeTable body (physTableOut body outStoreMap reservedVec))
      (argName s))))
    (hsave : ∀ base, OpResolves F W Q (abiLoadSave base))
    (hrdi : OpResolves F W Q abiSaveRdiName)
    (hmbr : ∀ b q, memrefBaseReload b = some q → OpResolves F W Q q)
    (hloadBase : isGpName loadBase = true) (hstoreBase : isGpName storeBase = true)
    (hcall : ∀ p ∈ callArgBaseReload, isGpName p.1 = true ∧ OpResolves F W Q p.2)
    (hout : ∀ p ∈ body.zipIdx, ∀ d tl opn srcs, p.1.li_i = .Lopn (d :: tl) opn srcs →
      numBindings body - outStoreMap.length ≤ posBidx body p.2 →
      posBidx body p.2 < numBindings body → AllocOp F W Q (rm d))
    (hpos : ∀ p ∈ body.zipIdx, PosOk F W Q rm shiftImm p.1.li_i) :
    encodableLcmd (CatCrypt.Crypto.Optimizer.LoadCSE.loadCSE (physBodyWithStores shiftImm body
      inLoadMap loadBase outStoreMap storeBase abiW memrefBaseReload callArgBaseReload
      reservedVec)) = true := by
  apply x86Enc_complete.encodable_of_legal
  rw [← hctx]
  exact lower_legal_loadCSE shiftImm body inLoadMap loadBase outStoreMap storeBase abiW
    memrefBaseReload callArgBaseReload reservedVec rm hrm habi hargs hsave hrdi hmbr hloadBase
    hstoreBase hcall hout hpos

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowerLegal
