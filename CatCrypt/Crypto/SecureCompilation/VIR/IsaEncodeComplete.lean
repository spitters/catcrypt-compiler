/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.IsaBackend
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.LegalizeIsa
public import CatCrypt.Crypto.Optimizer.LoadCSE

@[expose] public section

set_option autoImplicit false

/-!
# Encoder completeness on the spill legalisations of an instruction set

The encodability `B.encodable` of a back end `B : IsaBackend I` is read instruction by
instruction through an encoder `E : IsaEncoder`: a context of a body (for x86 the frame
size, the spill width and the save block), the encodability of an instruction in a context,
and the operand classes the encoder distinguishes. The law `EncoderComplete B E` ties the
two and states the operand facts the spill legalisations need. From it, every instruction
the legalisations of `LegalizeIsa` emit over allocated operands is encodable, and the load
forwarding `loadCSE` preserves encodability.

## Main definitions

* `isMovMnem`: the register-move mnemonics `MOV`, `MOV:64` and `MOVQ`.
* `IsaEncoder`: the context of a body, the encodability of an instruction in a context, the
  encoder registers, the resolving names, the spill slots with a frame offset, the memory
  names and the materialised comparisons the encoder builds, against a register and against
  an immediate.
* `AllocOpI`: an operand of the allocated body: an encoder register, or a spill slot with a
  frame offset.
* `EncoderComplete`: the encodability of a body is that of its instructions in the context
  of the body, and the operand laws of the encoder.
* `LegalForm`: the instruction forms the spill legalisations emit: register moves over
  resolving names with at most one memory name, the select over encoder registers, and the
  materialised comparisons the encoder builds over encoder registers, against a register or
  an immediate.

## Main results

* `EncoderComplete.encodable_of_instr`: a body whose instructions are encodable in its
  context is encodable.
* `EncoderComplete.encodable_of_legal`: a body whose instructions have legal forms in its
  context is encodable.
* `EncoderComplete.legalizeMovI_legal`, `legalizeOneSrcI_legal`, `cmovSpillSeqI_legal`,
  `setccSpillI?_legal`, `legalizeSpillDstI_legal`: the legalisations emit legal forms;
  `legalizeSpillDstI_cases`: an instruction of `legalizeSpillDstI` has a legal form or is the
  unlegalised instruction.
* `EncoderComplete.loadCSE_legalI`: `loadCSE` preserves legal forms;
  `EncoderComplete.encodable_of_legalized`: a legal body forwarded by `loadCSE` is encodable.
* `EncoderComplete.legalizeMovI_encodable`, `EncoderComplete.legalizeOneSrcI_encodable`:
  every instruction of a legalised register copy over allocated operands is encodable.
* `EncoderComplete.cmovSpillSeqI_encodable`: every instruction of the scratch select is
  encodable when the selected values are registers and the select mnemonic is `CMOV`.
* `EncoderComplete.setccSpillI?_encodable`: every instruction of the scratch comparison is
  encodable for a comparison the encoder builds.
* `EncoderComplete.legalizeSpillDstI_encodable`: the combination, with the encodability of
  the unlegalised instruction as the hypothesis of the fall-through arm.
* `EncoderComplete.loadCSE_encodableI`: `loadCSE` maps a body of instructions encodable in
  a context to a body of instructions encodable in that context.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## Register moves -/

/-- The register-move mnemonics of the exporter and its legalisations. -/
def isMovMnem (mn : String) : Bool := mn == "MOV" || mn == "MOV:64" || mn == "MOVQ"

theorem stripWidthTag_of_isMovMnem {mn : String} (hm : isMovMnem mn = true) :
    (stripWidthTag mn == "MOV" || stripWidthTag mn == "MOVQ") = true := by
  simp only [isMovMnem, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with (rfl | rfl) | rfl <;> decide +kernel

theorem isMovMnem_setccMov (opn : String) : isMovMnem (setccMov opn) = true := by
  unfold setccMov
  split <;> decide +kernel

theorem isMovMnem_of_isMov64Mnem {mn : String}
    (h : CatCrypt.Crypto.Optimizer.LoadCSE.isMov64Mnem mn = true) : isMovMnem mn = true := by
  simp only [CatCrypt.Crypto.Optimizer.LoadCSE.isMov64Mnem, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> decide +kernel

/-! ## The encoder -/

/-- **An instruction-level encoder**: the context `ctx body` of a body, the encodability
    `instr c i` of an instruction in a context, the names `reg` encoded as registers, the
    names `resolves c` an operand form resolves in a context, the spill slots `slot c` with
    a frame offset in a context, the names `memName` encoded as memory operands, and the
    materialised comparisons the encoder builds, `setcc` against a register and `setccImm`
    against an immediate. -/
structure IsaEncoder : Type 1 where
  /-- The context of a body. -/
  Ctx : Type
  /-- The context of a body. -/
  ctx : Lcmd → Ctx
  /-- Whether an instruction is encodable in a context. -/
  instr : Ctx → LinstrR → Bool
  /-- Whether a name is encoded as a register. -/
  reg : String → Bool
  /-- Whether a name resolves in a context. -/
  resolves : Ctx → String → Prop
  /-- Whether a name is a spill slot with a frame offset in a context. -/
  slot : Ctx → String → Prop
  /-- Whether a name is encoded as a memory operand. -/
  memName : String → Bool
  /-- Whether the encoder builds the materialised comparison with this mnemonic. -/
  setcc : String → Bool
  /-- Whether the encoder builds the materialised comparison with this mnemonic against this
      immediate. -/
  setccImm : String → Nat → Bool

/-- **An operand of the allocated body**: a name that is an encoder register, or a spill slot
    with a frame offset in the context `c`. -/
def AllocOpI (E : IsaEncoder) (c : E.Ctx) (o : LOperand) : Prop :=
  ∃ n, o = .reg n ∧ (E.reg n = true ∨ ((LOperand.reg n).isSpill = true ∧ E.slot c n))

/-- **The completeness law of an encoder** for the back end `B`: the encodability of a body
    is that of each of its instructions in the context of the body; the allocatable
    registers and the two reload scratch registers are encoder registers; an encoder
    register and a spill slot with a frame offset resolve; an encoder register is neither a
    spill slot nor a memory name; a spill slot is a memory name; a memory name is one of the
    load forwarding; a register move is encodable exactly when both names resolve and at
    most one is a memory name; the select at the select mnemonic of `I`, at width 64, over
    four encoder registers is encodable; and a materialised comparison the encoder builds
    over three encoder registers, or over two encoder registers and an immediate, is
    encodable. -/
structure EncoderComplete {I : Isa} (B : IsaBackend I) (E : IsaEncoder) : Prop where
  /-- The encodability of a body is that of its instructions in the context of the body. -/
  encodable_eq : ∀ body : Lcmd,
    B.encodable body = body.all fun i => E.instr (E.ctx body) i.li_i
  /-- An allocatable register is an encoder register. -/
  pool_reg : ∀ r ∈ I.allocPool, E.reg r = true
  /-- The primary reload scratch is an encoder register. -/
  reload_reg : E.reg I.reload = true
  /-- The secondary reload scratch is an encoder register. -/
  reloadSnd_reg : E.reg I.reloadSnd = true
  /-- An encoder register resolves. -/
  reg_resolves : ∀ (c : E.Ctx) (n : String), E.reg n = true → E.resolves c n
  /-- A spill slot with a frame offset resolves. -/
  slot_resolves : ∀ (c : E.Ctx) (n : String), E.slot c n → E.resolves c n
  /-- An encoder register is not a spill slot. -/
  reg_not_spill : ∀ n : String, E.reg n = true → (LOperand.reg n).isSpill = false
  /-- An encoder register is not a memory name. -/
  reg_not_mem : ∀ n : String, E.reg n = true → E.memName n = false
  /-- A spill slot is a memory name. -/
  spill_mem : ∀ n : String, (LOperand.reg n).isSpill = true → E.memName n = true
  /-- A memory name is a memory name of the load forwarding. -/
  mem_loadCSE : ∀ n : String, E.memName n = true →
    CatCrypt.Crypto.Optimizer.LoadCSE.isMemName n = true
  /-- A register move is encodable exactly when both names resolve and at most one is a
      memory name. -/
  mov_iff : ∀ (c : E.Ctx) (mn d s : String), isMovMnem mn = true →
    (E.instr c (.Lopn [.reg d] mn [.reg s]) = true ↔
      E.resolves c d ∧ E.resolves c s ∧ (E.memName d && E.memName s) = false)
  /-- The 64-bit select at the select mnemonic over four encoder registers is encodable. -/
  select_reg : ∀ m : String, I.selectMnemonic = some m → ∀ (c : E.Ctx) (dn cn tn fn : String),
    E.reg dn = true → E.reg cn = true → E.reg tn = true → E.reg fn = true →
    E.instr c (.Lopn [.reg dn] (withWidthTag 64 m) [.reg cn, .reg tn, .reg fn]) = true
  /-- A materialised comparison the encoder builds over three encoder registers is
      encodable. -/
  setcc_reg : ∀ (c : E.Ctx) (opn dn an sn : String), E.setcc opn = true →
    E.reg dn = true → E.reg an = true → E.reg sn = true →
    E.instr c (.Lopn [.reg dn] opn [.reg an, .reg sn]) = true
  /-- A materialised comparison the encoder builds against an immediate, over two encoder
      registers, is encodable. -/
  setccImm_reg : ∀ (c : E.Ctx) (opn dn an : String) (v : Nat), E.setccImm opn v = true →
    E.reg dn = true → E.reg an = true →
    E.instr c (.Lopn [.reg dn] opn [.reg an, .imm v]) = true

/-- **The legal forms of the spill legalisations** at the instruction set `I`, the encoder `E`
    and the context `c`: a register move whose two names resolve in `c` and of which at most
    one is a memory name; the 64-bit select at the select mnemonic of `I` over four encoder
    registers; a materialised comparison the encoder builds over three encoder registers; and
    a materialised comparison the encoder builds against an immediate over two encoder
    registers. -/
def LegalForm (I : Isa) (E : IsaEncoder) (c : E.Ctx) (i : LinstrR) : Prop :=
  (∃ mn d s, isMovMnem mn = true ∧ i = .Lopn [.reg d] mn [.reg s] ∧
      E.resolves c d ∧ E.resolves c s ∧ (E.memName d && E.memName s) = false) ∨
  (∃ m dn cn tn fn, I.selectMnemonic = some m ∧
      i = .Lopn [.reg dn] (withWidthTag 64 m) [.reg cn, .reg tn, .reg fn] ∧
      E.reg dn = true ∧ E.reg cn = true ∧ E.reg tn = true ∧ E.reg fn = true) ∨
  (∃ opn dn an sn, E.setcc opn = true ∧ i = .Lopn [.reg dn] opn [.reg an, .reg sn] ∧
      E.reg dn = true ∧ E.reg an = true ∧ E.reg sn = true) ∨
  (∃ opn dn an v, E.setccImm opn v = true ∧ i = .Lopn [.reg dn] opn [.reg an, .imm v] ∧
      E.reg dn = true ∧ E.reg an = true)

namespace EncoderComplete

variable {I : Isa} {B : IsaBackend I} {E : IsaEncoder} (h : EncoderComplete B E)
include h

/-- **A body whose instructions are encodable in its context is encodable.** -/
theorem encodable_of_instr {body : Lcmd}
    (hb : ∀ i ∈ body, E.instr (E.ctx body) i.li_i = true) : B.encodable body = true := by
  rw [h.encodable_eq]
  exact List.all_eq_true.2 hb

/-! ### Legal forms -/

/-- **An instruction of a legal form is encodable.** -/
theorem instr_of_legalForm {c : E.Ctx} {i : LinstrR} (hi : LegalForm I E c i) :
    E.instr c i = true := by
  rcases hi with ⟨mn, d, s, hm, rfl, hd, hs, hds⟩ |
    ⟨m, dn, cn, tn, fn, hsel, rfl, h1, h2, h3, h4⟩ | ⟨opn, dn, an, sn, ho, rfl, h1, h2, h3⟩ |
    ⟨opn, dn, an, v, ho, rfl, h1, h2⟩
  · exact (h.mov_iff c mn d s hm).2 ⟨hd, hs, hds⟩
  · exact h.select_reg m hsel c dn cn tn fn h1 h2 h3 h4
  · exact h.setcc_reg c opn dn an sn ho h1 h2 h3
  · exact h.setccImm_reg c opn dn an v ho h1 h2

/-- **A body whose instructions have legal forms in its context is encodable.** -/
theorem encodable_of_legal {body : Lcmd}
    (hb : ∀ i ∈ body, LegalForm I E (E.ctx body) i.li_i) : B.encodable body = true :=
  h.encodable_of_instr fun i hi => h.instr_of_legalForm (hb i hi)

/-! ### Allocated operands -/

/-- An allocated name resolves. -/
theorem allocOp_resolves {c : E.Ctx} {n : String} (ha : AllocOpI E c (.reg n)) :
    E.resolves c n := by
  obtain ⟨m, hm, hc⟩ := ha
  simp only [LOperand.reg.injEq] at hm
  subst hm
  rcases hc with hg | ⟨_, hs⟩
  · exact h.reg_resolves c n hg
  · exact h.slot_resolves c n hs

/-- An allocated name is a memory name exactly when it is a spill slot. -/
theorem allocOp_memName {c : E.Ctx} {n : String} (ha : AllocOpI E c (.reg n)) :
    E.memName n = (LOperand.reg n).isSpill := by
  obtain ⟨m, hm, hc⟩ := ha
  simp only [LOperand.reg.injEq] at hm
  subst hm
  rcases hc with hg | ⟨hk, _⟩
  · rw [h.reg_not_mem n hg, h.reg_not_spill n hg]
  · rw [h.spill_mem n hk, hk]

omit h in
/-- An allocated name that is not a spill slot is an encoder register. -/
theorem reg_of_allocOp_not_spill {c : E.Ctx} {n : String} (ha : AllocOpI E c (.reg n))
    (hs : (LOperand.reg n).isSpill = false) : E.reg n = true := by
  obtain ⟨m, hm, hc⟩ := ha
  simp only [LOperand.reg.injEq] at hm
  subst hm
  rcases hc with hg | ⟨hk, _⟩
  · exact hg
  · rw [hk] at hs; cases hs

/-- A move from an allocated operand to an encoder register has a legal form. -/
theorem legalForm_mov_left {c : E.Ctx} {mn r n : String} (hm : isMovMnem mn = true)
    (hr : E.reg r = true) (hn : AllocOpI E c (.reg n)) :
    LegalForm I E c (.Lopn [.reg r] mn [.reg n]) :=
  Or.inl ⟨mn, r, n, hm, rfl, h.reg_resolves c r hr, h.allocOp_resolves hn,
    by simp [h.reg_not_mem r hr]⟩

/-- A move from an encoder register to an allocated operand has a legal form. -/
theorem legalForm_mov_right {c : E.Ctx} {mn r n : String} (hm : isMovMnem mn = true)
    (hr : E.reg r = true) (hn : AllocOpI E c (.reg n)) :
    LegalForm I E c (.Lopn [.reg n] mn [.reg r]) :=
  Or.inl ⟨mn, n, r, hm, rfl, h.allocOp_resolves hn, h.reg_resolves c r hr,
    by simp [h.reg_not_mem r hr]⟩

/-- A move from an allocated operand to an encoder register is encodable. -/
theorem mov_reg_left {c : E.Ctx} {mn r n : String} (hm : isMovMnem mn = true)
    (hr : E.reg r = true) (hn : AllocOpI E c (.reg n)) :
    E.instr c (.Lopn [.reg r] mn [.reg n]) = true :=
  h.instr_of_legalForm (h.legalForm_mov_left hm hr hn)

/-- A move from an encoder register to an allocated operand is encodable. -/
theorem mov_reg_right {c : E.Ctx} {mn r n : String} (hm : isMovMnem mn = true)
    (hr : E.reg r = true) (hn : AllocOpI E c (.reg n)) :
    E.instr c (.Lopn [.reg n] mn [.reg r]) = true :=
  h.instr_of_legalForm (h.legalForm_mov_right hm hr hn)

/-! ### The legalised register copy -/

/-- **Every instruction of a legalised register copy over allocated operands has a legal
    form.** -/
theorem legalizeMovI_legal {c : E.Ctx} {d s : LOperand} {mov : String}
    (hm : isMovMnem mov = true) (hd : AllocOpI E c d) (hs : AllocOpI E c s) :
    ∀ i ∈ legalizeMovI I.toIsaAbi d s mov, LegalForm I E c i := by
  obtain ⟨dn, rfl, hd'⟩ := hd
  obtain ⟨sn, rfl, hs'⟩ := hs
  have hd : AllocOpI E c (.reg dn) := ⟨dn, rfl, hd'⟩
  have hs : AllocOpI E c (.reg sn) := ⟨sn, rfl, hs'⟩
  intro i hi
  unfold legalizeMovI at hi
  split_ifs at hi with hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact h.legalForm_mov_left hm h.reload_reg hs
    · exact h.legalForm_mov_right hm h.reload_reg hd
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    refine Or.inl ⟨mov, dn, sn, hm, rfl, h.allocOp_resolves hd, h.allocOp_resolves hs, ?_⟩
    rw [h.allocOp_memName hd, h.allocOp_memName hs]
    simpa using hb

/-- **Every instruction of a legalised register copy over allocated operands is
    encodable.** -/
theorem legalizeMovI_encodable {c : E.Ctx} {d s : LOperand} {mov : String}
    (hm : isMovMnem mov = true) (hd : AllocOpI E c d) (hs : AllocOpI E c s) :
    ∀ i ∈ legalizeMovI I.toIsaAbi d s mov, E.instr c i = true :=
  fun i hi => h.instr_of_legalForm (h.legalizeMovI_legal hm hd hs i hi)

/-- **Every instruction of the one-source arm of the allocation on a register move over
    allocated operands has a legal form.** -/
theorem legalizeOneSrcI_legal {c : E.Ctx} {u64 : Bool} {opn : String} {d s : LOperand}
    (hm : isMovMnem opn = true) (hd : AllocOpI E c d) (hs : AllocOpI E c s) :
    ∀ i ∈ legalizeOneSrcI I.toIsaAbi u64 opn d s, LegalForm I E c i := by
  have hsm : spillImmMovMnem u64 opn d s = opn := by
    obtain ⟨sn, rfl, -⟩ := hs
    rfl
  unfold legalizeOneSrcI
  rw [if_pos (stripWidthTag_of_isMovMnem hm), hsm]
  exact h.legalizeMovI_legal hm hd hs

/-- **Every instruction of the one-source arm of the allocation on a register move over
    allocated operands is encodable.** -/
theorem legalizeOneSrcI_encodable {c : E.Ctx} {u64 : Bool} {opn : String} {d s : LOperand}
    (hm : isMovMnem opn = true) (hd : AllocOpI E c d) (hs : AllocOpI E c s) :
    ∀ i ∈ legalizeOneSrcI I.toIsaAbi u64 opn d s, E.instr c i = true :=
  fun i hi => h.instr_of_legalForm (h.legalizeOneSrcI_legal hm hd hs i hi)

/-! ### The scratch select -/

/-- **Every instruction of the scratch select has a legal form** when the select mnemonic of
    the instruction set is `CMOV`, the destination and the condition are allocated, and the
    selected values are encoder registers. -/
theorem cmovSpillSeqI_legal (hsel : I.selectMnemonic = some "CMOV") {c : E.Ctx}
    {d cnd : LOperand} {tn fn : String}
    (hd : AllocOpI E c d) (hc : AllocOpI E c cnd) (ht : E.reg tn = true)
    (hf : E.reg fn = true) :
    ∀ i ∈ cmovSpillSeqI I.toIsaAbi "CMOV:64" d cnd (.reg tn) (.reg fn),
      LegalForm I E c i := by
  have hm64 : isMovMnem "MOV:64" = true := by decide +kernel
  have hsel' : ∀ dn cn : String, E.reg dn = true → E.reg cn = true →
      LegalForm I E c (.Lopn [.reg dn] "CMOV:64" [.reg cn, .reg tn, .reg fn]) :=
    fun dn cn hdn hcn =>
      Or.inr (Or.inl ⟨"CMOV", dn, cn, tn, fn, hsel, rfl, hdn, hcn, ht, hf⟩)
  obtain ⟨dn, rfl, hd'⟩ := hd
  obtain ⟨cn, rfl, hc'⟩ := hc
  have hd : AllocOpI E c (.reg dn) := ⟨dn, rfl, hd'⟩
  have hc : AllocOpI E c (.reg cn) := ⟨cn, rfl, hc'⟩
  intro i hi
  unfold cmovSpillSeqI at hi
  cases hcs : (LOperand.reg cn).isSpill <;> cases hds : (LOperand.reg dn).isSpill <;>
    simp only [hcs, hds, if_true, if_false, Bool.false_eq_true, List.nil_append,
      List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  · subst hi
    exact hsel' dn cn (reg_of_allocOp_not_spill hd hds) (reg_of_allocOp_not_spill hc hcs)
  · rcases hi with rfl | rfl
    · exact hsel' _ cn h.reload_reg (reg_of_allocOp_not_spill hc hcs)
    · exact h.legalForm_mov_right hm64 h.reload_reg hd
  · rcases hi with rfl | rfl
    · exact h.legalForm_mov_left hm64 h.reloadSnd_reg hc
    · exact hsel' dn _ (reg_of_allocOp_not_spill hd hds) h.reloadSnd_reg
  · rcases hi with rfl | rfl | rfl
    · exact h.legalForm_mov_left hm64 h.reloadSnd_reg hc
    · exact hsel' _ _ h.reload_reg h.reloadSnd_reg
    · exact h.legalForm_mov_right hm64 h.reload_reg hd

/-- **Every instruction of the scratch select is encodable** when the select mnemonic of the
    instruction set is `CMOV`, the destination and the condition are allocated, and the
    selected values are encoder registers. -/
theorem cmovSpillSeqI_encodable (hsel : I.selectMnemonic = some "CMOV") {c : E.Ctx}
    {d cnd : LOperand} {tn fn : String}
    (hd : AllocOpI E c d) (hc : AllocOpI E c cnd) (ht : E.reg tn = true)
    (hf : E.reg fn = true) :
    ∀ i ∈ cmovSpillSeqI I.toIsaAbi "CMOV:64" d cnd (.reg tn) (.reg fn),
      E.instr c i = true :=
  fun i hi => h.instr_of_legalForm (h.cmovSpillSeqI_legal hsel hd hc ht hf i hi)

/-! ### The scratch comparison -/

/-- **Every instruction of the scratch comparison has a legal form** for a comparison the
    encoder builds, over allocated operands. -/
theorem setccSpillI?_legal {c : E.Ctx} {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} {l : List LinstrR} (hl : setccSpillI? I.toIsaAbi dsts opn srcs = some l)
    (ho : E.setcc opn = true) (hd : ∀ o ∈ dsts, AllocOpI E c o)
    (hs : ∀ o ∈ srcs, AllocOpI E c o) :
    ∀ i ∈ l, LegalForm I E c i := by
  unfold setccSpillI? at hl
  split at hl
  · rename_i d a b
    split_ifs at hl
    cases hl
    have ha := hs (.reg a) (by simp)
    have hb := hs (.reg b) (by simp)
    have hm := isMovMnem_setccMov opn
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact h.legalForm_mov_left hm h.reload_reg ha
    · exact h.legalForm_mov_left hm h.reloadSnd_reg hb
    · exact Or.inr (Or.inr (Or.inl ⟨opn, _, _, _, ho, rfl, h.reload_reg, h.reload_reg,
        h.reloadSnd_reg⟩))
    · obtain ⟨dn, rfl, hd'⟩ := hd d (by simp)
      exact h.legalForm_mov_right hm h.reload_reg ⟨dn, rfl, hd'⟩
  · cases hl

/-- **Every instruction of the scratch comparison is encodable** for a comparison the encoder
    builds, over allocated operands. -/
theorem setccSpillI?_encodable {c : E.Ctx} {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} {l : List LinstrR} (hl : setccSpillI? I.toIsaAbi dsts opn srcs = some l)
    (ho : E.setcc opn = true) (hd : ∀ o ∈ dsts, AllocOpI E c o)
    (hs : ∀ o ∈ srcs, AllocOpI E c o) :
    ∀ i ∈ l, E.instr c i = true :=
  fun i hi => h.instr_of_legalForm (h.setccSpillI?_legal hl ho hd hs i hi)

/-! ### The spill legalisation of a general instruction -/

/-- **The instructions of `legalizeSpillDstI`**, for allocated operands, when the select
    mnemonic of the instruction set is `CMOV`: each has a legal form (the scratch select when
    its selected values are encoder registers, the scratch comparison when the encoder builds
    it), or it is the unlegalised instruction, emitted when neither the select nor the
    comparison applies. -/
theorem legalizeSpillDstI_cases (hsel' : I.selectMnemonic = some "CMOV") {c : E.Ctx}
    {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    (hd : ∀ o ∈ dsts, AllocOpI E c o) (hs : ∀ o ∈ srcs, AllocOpI E c o)
    (hsel : ∀ cnd t f, srcs = [cnd, t, f] → opn = "CMOV:64" →
      ∃ tn fn, t = .reg tn ∧ f = .reg fn ∧ E.reg tn = true ∧ E.reg fn = true)
    (hcmp : isSetccMnem opn = true → E.setcc opn = true) :
    ∀ i ∈ legalizeSpillDstI I.toIsaAbi dsts opn srcs, LegalForm I E c i ∨
      (cmovSpillDstI? I.toIsaAbi dsts opn srcs = none ∧
        setccSpillI? I.toIsaAbi dsts opn srcs = none ∧ i = .Lopn dsts opn srcs) := by
  unfold legalizeSpillDstI
  cases hc : cmovSpillDstI? I.toIsaAbi dsts opn srcs with
  | some l =>
    simp only
    unfold cmovSpillDstI? at hc
    split at hc
    · rename_i d cnd t f
      split_ifs at hc with hb
      cases hc
      have hop : opn = "CMOV:64" := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        exact hb.2
      obtain ⟨tn, fn, rfl, rfl, ht, hf⟩ := hsel cnd t f rfl hop
      subst hop
      exact fun i hi =>
        Or.inl (h.cmovSpillSeqI_legal hsel' (hd d (by simp)) (hs cnd (by simp)) ht hf i hi)
    · cases hc
  | none =>
    cases hs' : setccSpillI? I.toIsaAbi dsts opn srcs with
    | some l =>
      simp only
      have hset : isSetccMnem opn = true := by
        unfold setccSpillI? at hs'
        split at hs'
        · split_ifs at hs' with hb
          · exact (Bool.and_eq_true _ _ ▸ hb).2
        · cases hs'
      exact fun i hi => Or.inl (h.setccSpillI?_legal hs' (hcmp hset) hd hs i hi)
    | none =>
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro i rfl
      exact Or.inr ⟨trivial, trivial, rfl⟩

/-- **Every instruction of `legalizeSpillDstI` has a legal form**, for allocated operands,
    when the select mnemonic of the instruction set is `CMOV`: the scratch select when its
    selected values are encoder registers, the scratch comparison when the encoder builds it,
    and the single instruction when it has a legal form itself. -/
theorem legalizeSpillDstI_legal (hsel' : I.selectMnemonic = some "CMOV") {c : E.Ctx}
    {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    (hd : ∀ o ∈ dsts, AllocOpI E c o) (hs : ∀ o ∈ srcs, AllocOpI E c o)
    (hsel : ∀ cnd t f, srcs = [cnd, t, f] → opn = "CMOV:64" →
      ∃ tn fn, t = .reg tn ∧ f = .reg fn ∧ E.reg tn = true ∧ E.reg fn = true)
    (hcmp : isSetccMnem opn = true → E.setcc opn = true)
    (hone : cmovSpillDstI? I.toIsaAbi dsts opn srcs = none →
      setccSpillI? I.toIsaAbi dsts opn srcs = none →
      LegalForm I E c (.Lopn dsts opn srcs)) :
    ∀ i ∈ legalizeSpillDstI I.toIsaAbi dsts opn srcs, LegalForm I E c i := by
  intro i hi
  rcases h.legalizeSpillDstI_cases hsel' hd hs hsel hcmp i hi with hl | ⟨hc, hs', rfl⟩
  · exact hl
  · exact hone hc hs'

/-- **Every instruction of `legalizeSpillDstI` is encodable**, for allocated operands, when the
    select mnemonic of the instruction set is `CMOV`: the scratch select when its selected
    values are encoder registers, the scratch comparison when the encoder builds it, and the
    single instruction when it is itself encodable. -/
theorem legalizeSpillDstI_encodable (hsel' : I.selectMnemonic = some "CMOV") {c : E.Ctx}
    {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    (hd : ∀ o ∈ dsts, AllocOpI E c o) (hs : ∀ o ∈ srcs, AllocOpI E c o)
    (hsel : ∀ cnd t f, srcs = [cnd, t, f] → opn = "CMOV:64" →
      ∃ tn fn, t = .reg tn ∧ f = .reg fn ∧ E.reg tn = true ∧ E.reg fn = true)
    (hcmp : isSetccMnem opn = true → E.setcc opn = true)
    (hone : cmovSpillDstI? I.toIsaAbi dsts opn srcs = none →
      setccSpillI? I.toIsaAbi dsts opn srcs = none →
      E.instr c (.Lopn dsts opn srcs) = true) :
    ∀ i ∈ legalizeSpillDstI I.toIsaAbi dsts opn srcs, E.instr c i = true := by
  intro i hi
  rcases h.legalizeSpillDstI_cases hsel' hd hs hsel hcmp i hi with hl | ⟨hc, hs', rfl⟩
  · exact h.instr_of_legalForm hl
  · exact hone hc hs'

/-! ### Load forwarding -/

section LoadCSE

open CatCrypt.Crypto.Optimizer.LoadCSE

omit h in
/-- The load environment holds only names that resolve in the context `c`. -/
def EnvResolvesI (E : IsaEncoder) (c : E.Ctx) (env : LoadEnv) : Prop :=
  ∀ p ∈ env, E.resolves c p.2

/-- **One forwarding step preserves a predicate `P` on instructions** and keeps the
    environment resolving, when every register move satisfying `P` has a resolving
    destination, and every register move over two resolving names of which at most one is a
    memory name satisfies `P`. -/
theorem stepLoad_preservesI {c : E.Ctx} (P : LinstrR → Prop)
    (hres : ∀ mn d s, isMovMnem mn = true → P (.Lopn [.reg d] mn [.reg s]) → E.resolves c d)
    (hmov : ∀ mn d s, isMovMnem mn = true → E.resolves c d → E.resolves c s →
      (E.memName d && E.memName s) = false → P (.Lopn [.reg d] mn [.reg s]))
    (env : LoadEnv) (i : Linstr) (hh : EnvResolvesI E c env) (hi : P i.li_i) :
    P (stepLoad env i).1.li_i ∧ EnvResolvesI E c (stepLoad env i).2 := by
  cases hr : asWideReload i.li_i with
  | none =>
    refine ⟨by simp only [stepLoad, hr]; exact hi, ?_⟩
    simp only [stepLoad, hr]
    intro p hp
    exact hh p ((mem_foldl_killReg _ _ p (mem_foldl_killSlot _ _ p hp).1).1)
  | some dsm =>
    obtain ⟨d, s, mn⟩ := dsm
    obtain ⟨hli, hm⟩ := asWideReload_eq hr
    have hmv := isMovMnem_of_isMov64Mnem hm
    rw [hli] at hi
    have hd := hres mn d s hmv hi
    have henv : EnvResolvesI E c (((env.killReg d).killSlot d).set s d) := by
      intro p hp
      rcases CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad.mem_set hp with
        ⟨hp', _⟩ | rfl
      · exact hh p (mem_killReg (mem_killSlot hp').1).1
      · exact hd
    cases hf : env.find s with
    | none =>
      simp only [stepLoad, hr, hf]
      exact ⟨by rw [hli]; exact hi, henv⟩
    | some r =>
      have hrr : E.resolves c r :=
        hh (s, r) (CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad.mem_of_find hf)
      by_cases hrd : r = d
      · simp only [stepLoad, hr, hf, hrd, if_true]
        exact ⟨by rw [hli]; exact hi, by simpa [hrd] using henv⟩
      · by_cases hmm : isMemName d = true ∧ isMemName r = true
        · simp only [stepLoad, hr, hf, hrd, if_false, if_pos hmm]
          exact ⟨by rw [hli]; exact hi, henv⟩
        · simp only [stepLoad, hr, hf, hrd, if_false, if_neg hmm]
          refine ⟨hmov mn d r hmv hd hrr ?_, henv⟩
          cases hed : E.memName d <;> cases her : E.memName r
          all_goals first
            | rfl
            | exact absurd ⟨h.mem_loadCSE d hed, h.mem_loadCSE r her⟩ hmm

/-- **`loadCSE` preserves a predicate `P` on instructions** under the hypotheses of
    `stepLoad_preservesI`: a body of instructions satisfying `P` is forwarded to a body of
    instructions satisfying `P`. -/
theorem loadCSE_preservesI {c : E.Ctx} (P : LinstrR → Prop)
    (hres : ∀ mn d s, isMovMnem mn = true → P (.Lopn [.reg d] mn [.reg s]) → E.resolves c d)
    (hmov : ∀ mn d s, isMovMnem mn = true → E.resolves c d → E.resolves c s →
      (E.memName d && E.memName s) = false → P (.Lopn [.reg d] mn [.reg s]))
    (body : List Linstr) (hb : ∀ i ∈ body, P i.li_i) :
    ∀ i ∈ loadCSE body, P i.li_i := by
  rw [loadCSE_eq]
  suffices ∀ (env : LoadEnv) (b : List Linstr), EnvResolvesI E c env →
      (∀ i ∈ b, P i.li_i) → ∀ i ∈ loadCSEAux env b, P i.li_i from
    this [] body (fun _ hp => by simp at hp) hb
  intro env b
  induction b generalizing env with
  | nil => intro _ _ i hi; simp at hi
  | cons j js ih =>
    intro hh hjs i hi
    rw [loadCSEAux_cons, List.mem_cons] at hi
    have hstep := h.stepLoad_preservesI P hres hmov env j hh (hjs j List.mem_cons_self)
    rcases hi with rfl | hi
    · exact hstep.1
    · exact ih _ hstep.2 (fun k hk => hjs k (List.mem_cons_of_mem j hk)) i hi

/-- **One forwarding step keeps an instruction encodable in a context** and the environment
    resolving. -/
theorem stepLoad_encodableI {c : E.Ctx} (env : LoadEnv) (i : Linstr)
    (hh : EnvResolvesI E c env) (hi : E.instr c i.li_i = true) :
    E.instr c (stepLoad env i).1.li_i = true ∧ EnvResolvesI E c (stepLoad env i).2 :=
  h.stepLoad_preservesI (fun i => E.instr c i = true)
    (fun mn d s hm hi => ((h.mov_iff c mn d s hm).1 hi).1)
    (fun mn d s hm hd hs hds => (h.mov_iff c mn d s hm).2 ⟨hd, hs, hds⟩) env i hh hi

/-- **`loadCSE` preserves encodability in a context**: a body of instructions encodable in
    the context `c` is forwarded to a body of instructions encodable in `c`. -/
theorem loadCSE_encodableI {c : E.Ctx} (body : List Linstr)
    (hb : ∀ i ∈ body, E.instr c i.li_i = true) :
    ∀ i ∈ loadCSE body, E.instr c i.li_i = true :=
  h.loadCSE_preservesI (fun i => E.instr c i = true)
    (fun mn d s hm hi => ((h.mov_iff c mn d s hm).1 hi).1)
    (fun mn d s hm hd hs hds => (h.mov_iff c mn d s hm).2 ⟨hd, hs, hds⟩) body hb

/-- **`loadCSE` preserves legal forms in a context**: a body of instructions with legal forms
    in the context `c` is forwarded to a body of instructions with legal forms in `c`. -/
theorem loadCSE_legalI {c : E.Ctx} (body : List Linstr)
    (hb : ∀ i ∈ body, LegalForm I E c i.li_i) :
    ∀ i ∈ loadCSE body, LegalForm I E c i.li_i :=
  h.loadCSE_preservesI (LegalForm I E c)
    (fun mn d s hm hi => ((h.mov_iff c mn d s hm).1 (h.instr_of_legalForm hi)).1)
    (fun mn d s hm hd hs hds => Or.inl ⟨mn, d, s, hm, rfl, hd, hs, hds⟩) body hb

/-- **The legalised body after load forwarding is encodable**: a body of instructions with
    legal forms in the context of its forwarded body is forwarded by `loadCSE` to an
    encodable body. -/
theorem encodable_of_legalized (body : List Linstr)
    (hb : ∀ i ∈ body, LegalForm I E (E.ctx (loadCSE body)) i.li_i) :
    B.encodable (loadCSE body) = true :=
  h.encodable_of_legal (h.loadCSE_legalI body hb)

end LoadCSE

end EncoderComplete

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
