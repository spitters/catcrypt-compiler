/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.TakeDrop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrMnemDispatch
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody
public import CatCrypt.Crypto.SecureCompilation.VIR.IsaEncodeComplete

@[expose] public section

set_option autoImplicit false

/-!
# Encoder completeness on the spill legalisations

The checked encoder `LprogBytes.encodeLcmdChecked` accepts a body exactly when every
instruction satisfies `encodableLinstrR`. This module proves that predicate on the
instructions the spill legalisations of the physical-ABI allocation
(`physBodyWithStores`) emit, and its preservation by the load forwarding `loadCSE`.

## Operands

The allocation renames every operand of a one-source move, a select and a
materialised comparison to a general-purpose register or a spill slot `k.N`
(`AllocOp`). A name resolves when it is a general-purpose register, a frame slot whose
offset `spillQsaveOff` parses, or a `mem.*` cell whose base is a general-purpose
register (`OpResolves`). The encoder addresses
a name as memory when it is a frame slot or a `mem.*` cell (`encMemName`).

## Main definitions

* `x86Alu`, `x86AluImm`, `x86ShiftReg`, `x86Unary`, `x86MemMov`, `x86SibLoad`,
  `x86SibStore`, `x86Carry3`, `x86FlagOut`, `x86WideMul`, `x86StoreImm`, `x86ZeroArr`,
  `x86SlotImm`, `x86Fixed`: the instruction families the x86 encoder builds beyond the register moves, the select and the
  materialised comparisons.
* `x86Enc`: the x86 instance of the instruction-level encoder `IsaEncoder`.
* `opResolvesB`, `x86LegalB`: the decisions of `OpResolves` and of the legal forms
  `LegalForm` at the x86 encoder.
* `VIR.LprogIsa.x86Backend`: the x86 back end, whose legal instructions are those of a legal
  form of the x86 encoder in the context of the body.

## Main results

* `x86Enc_complete`: the x86 encoder satisfies the completeness law `EncoderComplete` for
  the x86 back end; the results on the legalisations and on `loadCSE` below are its
  instances through the generic theorems of `IsaEncodeComplete`.
* `encTwoAddr_ne_nil_iff`: the two-address form has bytes exactly when one name is a
  general-purpose register and the other resolves; `encTwoAddr_ne_nil`: so when both
  names resolve and at most one is a memory name; `opResolves_of_encTwoAddr`: a form
  with bytes has resolving names.
* `encodableLinstrR_mov_iff`, `encodableLinstrR_mov`: a register move `MOV`, `MOV:64`
  or `MOVQ` is encodable exactly when its two-address form has bytes, so under the
  same conditions.
* `legalizeMov_encodable`, `legalizeOneSrc_encodable`: every instruction of a
  legalised register copy over allocated operands is encodable.
* `cmovSpillSeq_encodable`: every instruction of the scratch select is encodable when
  the selected values are registers.
* `setccSpill?_encodable`: every instruction of the scratch comparison is encodable
  for the comparisons `SETE` and `SETNE`.
* `legalizeSpillDst_encodable`: the combination, with the encodability of the
  unlegalised instruction as the hypothesis of the fall-through arm.
* `encodableLinstrR_movImm_gp`, `encodableLinstrR_movImm_slot`, `encodableLinstrR_alu`,
  `encodableLinstrR_aluImm`, `encodableLinstrR_shiftReg`, `encodableLinstrR_unary`,
  `encodableLinstrR_memMov`, `encodableLinstrR_sibLoad`, `encodableLinstrR_sibStore`,
  `encodableLinstrR_carry3`, `encodableLinstrR_flagOut`, `encodableLinstrR_wideMul`,
  `encodableLinstrR_storeImm`, `encodableLinstrR_zeroArr`, `encodableLinstrR_fixed`: each family is encodable over general-purpose registers (and,
  for the immediate move and the loads and stores, over resolving names).
* `loadCSE_encodable`: `loadCSE` maps a body of encodable instructions to a body of
  encodable instructions, at the same frame size, spill width and save block.
* `encodable_of_legal_x86`, `encodable_of_legalized_x86`: a body of instructions with legal
  forms (`LegalForm`) is encodable, and so is its forwarding by `loadCSE`.
* `x86LegalB_iff`, `VIR.LprogIsa.x86Backend_legal`: `x86LegalB` decides `LegalForm`.
* `VIR.LprogIsa.x86Backend_encodable_of_legal`: the law `IsaBackend.Laws.encodable_of_legal`
  at the x86 back end.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeComplete

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (isMovMnem IsaEncoder AllocOpI
  EncoderComplete LegalForm)

/-! ## Non-empty byte forms -/

theorem encAluRRw_ne_nil (w op d s : Nat) : encAluRRw w op d s ≠ [] := by
  simp [encAluRRw]

theorem enc0FRRw_ne_nil (w op d s : Nat) : enc0FRRw w op d s ≠ [] := by
  simp [enc0FRRw]

theorem encMemMovw_ne_nil (w op r base : Nat) (off : Int) : encMemMovw w op r base off ≠ [] := by
  simp [encMemMovw]

theorem encRspMem_ne_nil (w op r : Nat) (off : Int) : encRspMem w op r off ≠ [] := by
  unfold encRspMem
  split_ifs <;> simp

theorem encCmovSelect_ne_nil (w dn cn tn fn : Nat) : encCmovSelect w dn cn tn fn ≠ [] := by
  unfold encCmovSelect
  split_ifs <;> simp [encAluRRw]

theorem encSetccCmp_ne_nil (w op d a b : Nat) : encSetccCmp w op d a b ≠ [] := by
  simp [encSetccCmp, encAluRRw]

theorem encSetccCmpImm_ne_nil (w op d a v : Nat) : encSetccCmpImm w op d a v ≠ [] := by
  simp [encSetccCmpImm, encSetccReg]

/-! ## Operand classes -/

/-- A name the two-address form resolves: a general-purpose register, a frame slot
    (`k.N`, `qsave.X`) whose frame offset parses, or a `mem.*` cell whose base is a
    general-purpose register. -/
def OpResolves (F W Q : Nat) (n : String) : Prop :=
  isGpName n = true ∨ (spillQsaveOff F W n Q).isSome = true ∨ (parseMemNameGp n).isSome = true

/-- A name the encoder addresses as memory: a frame slot or a `mem.*` cell. -/
def encMemName (n : String) : Bool := isSpillOrQsave n || (parseMemName n).isSome

/-- An operand of the allocated body: a general-purpose register, or a spill slot
    `k.N` whose frame offset resolves. -/
def AllocOp (F W Q : Nat) (o : LOperand) : Prop :=
  ∃ n, o = .reg n ∧
    (isGpName n = true ∨ (hasPrefix n "k." = true ∧ (spillQsaveOff F W n Q).isSome = true))

theorem isSpillOrQsave_of_spillQsaveOff {F W Q : Nat} {n : String} {off : Int}
    (h : spillQsaveOff F W n Q = some off) : isSpillOrQsave n = true := by
  unfold spillQsaveOff at h
  unfold isSpillOrQsave
  by_cases hk : hasPrefix n "k." = true
  · simp [hk]
  · by_cases hq : hasPrefix n "qsave." = true
    · simp [hq]
    · simp [hk, hq] at h

theorem spillQsaveOff_of_not {F W Q : Nat} {n : String} (h : isSpillOrQsave n = false) :
    spillQsaveOff F W n Q = none := by
  cases ho : spillQsaveOff F W n Q with
  | none => rfl
  | some off => rw [isSpillOrQsave_of_spillQsaveOff ho] at h; cases h

theorem hasPrefix_mem_of_parseMemName {n : String} {p : Nat × Int}
    (h : parseMemName n = some p) : hasPrefix n "mem." = true := by
  unfold parseMemName at h
  by_cases hm : hasPrefix n "mem." = true
  · exact hm
  · simp [hm] at h

theorem opResolves_of_isGpName {F W Q : Nat} {n : String} (h : isGpName n = true) :
    OpResolves F W Q n := Or.inl h

theorem isGpName_of_spillQsaveOff {F W Q : Nat} {n : String} {off : Int}
    (h : spillQsaveOff F W n Q = some off) : isGpName n = false := by
  cases hg : isGpName n
  · rfl
  · have hq := (notSlotMem_of_isGpName hg).1
    rw [isSpillOrQsave_of_spillQsaveOff h] at hq; cases hq

theorem isGpName_of_parseMemName {n : String} {p : Nat × Int} (h : parseMemName n = some p) :
    isGpName n = false := by
  cases hg : isGpName n
  · rfl
  · rw [(notSlotMem_of_isGpName hg).2] at h; cases h

theorem encMemName_of_isGpName {n : String} (h : isGpName n = true) : encMemName n = false := by
  have := notSlotMem_of_isGpName h
  simp [encMemName, this.1, this.2]

theorem isGpName_of_hasPrefix_k {n : String} (hk : hasPrefix n "k." = true) :
    isGpName n = false := by
  unfold isGpName
  split <;> first | rfl | (exfalso; revert hk; decide)

theorem isSpill_reg (n : String) : (LOperand.reg n).isSpill = hasPrefix n "k." := by
  simp [LOperand.isSpill, PhysAbiShape.isPrefixOf_eq_list, hasPrefix]

theorem isSpillOrQsave_of_k {n : String} (hk : hasPrefix n "k." = true) :
    isSpillOrQsave n = true := by
  simp [isSpillOrQsave, hk]

/-- An allocated name resolves. -/
theorem AllocOp.opResolves {F W Q : Nat} {n : String} (h : AllocOp F W Q (.reg n)) :
    OpResolves F W Q n := by
  obtain ⟨m, hm, hc⟩ := h
  simp only [LOperand.reg.injEq] at hm
  subst hm
  rcases hc with hg | ⟨_, hs⟩
  · exact Or.inl hg
  · exact Or.inr (Or.inl hs)

/-- A resolving name the encoder does not address as memory is a general-purpose
    register. -/
theorem isGpName_of_opResolves {F W Q : Nat} {n : String} (h : OpResolves F W Q n)
    (hm : encMemName n = false) : isGpName n = true := by
  rcases h with hg | hs | hp
  · exact hg
  · obtain ⟨off, ho⟩ := Option.isSome_iff_exists.1 hs
    simp [encMemName, isSpillOrQsave_of_spillQsaveOff ho] at hm
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hp
    simp [encMemName, parseMemName_of_parseMemNameGp hp] at hm

/-- An allocated name is a memory name exactly when it is a spill slot. -/
theorem AllocOp.encMemName_eq {F W Q : Nat} {n : String} (h : AllocOp F W Q (.reg n)) :
    encMemName n = (LOperand.reg n).isSpill := by
  obtain ⟨m, hm, hc⟩ := h
  simp only [LOperand.reg.injEq] at hm
  subst hm
  rw [isSpill_reg]
  rcases hc with hg | ⟨hk, _⟩
  · rw [encMemName_of_isGpName hg]
    cases hk : hasPrefix n "k."
    · rfl
    · rw [isGpName_of_hasPrefix_k hk] at hg; cases hg
  · simp [encMemName, isSpillOrQsave_of_k hk, hk]

theorem isGpName_R15 : isGpName reloadScratch = true := by decide +kernel
theorem isGpName_R14 : isGpName reloadScratch2 = true := by decide +kernel

theorem allocOp_gp {F W Q : Nat} {n : String} (h : isGpName n = true) :
    AllocOp F W Q (.reg n) := ⟨n, rfl, Or.inl h⟩

/-! ## The two-address form -/

/-- **The two-address form has bytes exactly on the resolvable operand pairs**: one
    name is a general-purpose register and the other resolves (a register, a frame
    slot whose offset parses, or a `mem.*` cell with a general-purpose base). -/
theorem encTwoAddr_ne_nil_iff {F W Q w op : Nat} {d s : String} :
    encTwoAddr F W w op (.reg d) (.reg s) Q ≠ [] ↔
      (isGpName d = true ∧ OpResolves F W Q s) ∨ (OpResolves F W Q d ∧ isGpName s = true) := by
  unfold encTwoAddr OpResolves
  cases hod : spillQsaveOff F W d Q with
  | some od =>
    have hgd := isGpName_of_spillQsaveOff hod
    cases hos : spillQsaveOff F W s Q with
    | some os =>
      simp [hod, hos, hgd, isGpName_of_spillQsaveOff hos]
    | none =>
      cases hgs : isGpName s <;> simp [hod, hos, hgd, hgs, encRspMem_ne_nil]
  | none =>
    cases hos : spillQsaveOff F W s Q with
    | some os =>
      have hgs := isGpName_of_spillQsaveOff hos
      cases hgd : isGpName d <;> simp [hod, hos, hgd, hgs, encRspMem_ne_nil]
    | none =>
      cases hpd : parseMemNameGp d with
      | some pd =>
        obtain ⟨bd, od⟩ := pd
        have hgd := isGpName_of_parseMemName (parseMemName_of_parseMemNameGp hpd)
        cases hps : parseMemNameGp s with
        | some ps =>
          obtain ⟨bs, os⟩ := ps
          simp [hod, hos, hpd, hps, hgd,
            isGpName_of_parseMemName (parseMemName_of_parseMemNameGp hps)]
        | none =>
          cases hgs : isGpName s <;> simp [hod, hos, hpd, hps, hgd, hgs, encMemMovw_ne_nil]
      | none =>
        cases hps : parseMemNameGp s with
        | some ps =>
          obtain ⟨bs, os⟩ := ps
          have hgs := isGpName_of_parseMemName (parseMemName_of_parseMemNameGp hps)
          cases hgd : isGpName d <;> simp [hod, hos, hpd, hps, hgd, hgs, encMemMovw_ne_nil]
        | none =>
          cases hgd : isGpName d <;> cases hgs : isGpName s <;>
            simp [hod, hos, hpd, hps, hgd, hgs, encAluRRw_ne_nil]

/-- **The two-address form has bytes** when both names resolve and at most one is a
    memory name. -/
theorem encTwoAddr_ne_nil {F W Q w op : Nat} {d s : String}
    (hd : OpResolves F W Q d) (hs : OpResolves F W Q s)
    (hm : (encMemName d && encMemName s) = false) :
    encTwoAddr F W w op (.reg d) (.reg s) Q ≠ [] := by
  refine encTwoAddr_ne_nil_iff.2 ?_
  cases hmd : encMemName d
  · exact Or.inl ⟨isGpName_of_opResolves hd hmd, hs⟩
  · rw [hmd, Bool.true_and] at hm
    exact Or.inr ⟨hd, isGpName_of_opResolves hs hm⟩

/-- **A two-address form with bytes has resolving names.** -/
theorem opResolves_of_encTwoAddr {F W Q w op : Nat} {d s : String}
    (h : encTwoAddr F W w op (.reg d) (.reg s) Q ≠ []) :
    OpResolves F W Q d ∧ OpResolves F W Q s := by
  rcases encTwoAddr_ne_nil_iff.1 h with ⟨hd, hs⟩ | ⟨hd, hs⟩
  · exact ⟨Or.inl hd, hs⟩
  · exact ⟨hd, Or.inl hs⟩

/-! ## Register moves -/

/-- The one-source dispatch of a two-address mnemonic at the width of its tag. -/
theorem dispatch_alu_one_w
    (frame spillW op : Nat) (mnem base : String) (dn sn : String) (qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none) (halu : aluOpcode base = some op)
    (htag : tagShiftExt base = none) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg sn]) qsaveB
      = encTwoAddr frame spillW (rexW (mnemWidth mnem)) op (.reg dn) (.reg sn) qsaveB := by
  simp only [encodeLopn, hbind, hstrip, hmulx, hmulxmem, hadx, halu, htag,
    Bool.false_eq_true, if_false]

/-- A register move dispatches to the two-address move form. -/
theorem encodeLopn_movAny {F W Q : Nat} {mn : String} (d s : String) (hm : isMovMnem mn = true) :
    encodeLopn F W (.Lopn [.reg d] mn [.reg s]) Q
      = encTwoAddr F W (rexW (mnemWidth mn)) 0x89 (.reg d) (.reg s) Q := by
  simp only [isMovMnem, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with (rfl | rfl) | rfl
  · exact dispatch_alu_one_w F W 0x89 "MOV" "MOV" d s Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact dispatch_alu_one_w F W 0x89 "MOV:64" "MOV" d s Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact dispatch_alu_one_w F W 0x89 "MOVQ" "MOVQ" d s Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

theorem carriesNoBytes_mov {mn : String} (d s : String) (hm : isMovMnem mn = true) :
    carriesNoBytes (.Lopn [.reg d] mn [.reg s]) = false := by
  simp only [isMovMnem, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with (rfl | rfl) | rfl <;>
    simp [carriesNoBytes, show isMulHiBinding "MOV" = false from by decide +kernel,
      show isMulHiBinding "MOV:64" = false from by decide +kernel,
      show isMulHiBinding "MOVQ" = false from by decide +kernel,
      show isIdentityTagShift "MOV" = false from by decide +kernel,
      show isIdentityTagShift "MOV:64" = false from by decide +kernel,
      show isIdentityTagShift "MOVQ" = false from by decide +kernel]

/-- A register move is encodable exactly when its two-address form has bytes. -/
theorem encodableLinstrR_mov_iff {F W Q : Nat} {mn d s : String} (hm : isMovMnem mn = true) :
    encodableLinstrR F W (.Lopn [.reg d] mn [.reg s]) Q = true ↔
      encTwoAddr F W (rexW (mnemWidth mn)) 0x89 (.reg d) (.reg s) Q ≠ [] := by
  simp [encodableLinstrR, encodeLinstrR, encodeLopn_movAny d s hm, carriesNoBytes_mov d s hm]

/-- **A register move is encodable** when both names resolve and at most one is a
    memory name. -/
theorem encodableLinstrR_mov {F W Q : Nat} {mn d s : String} (hm : isMovMnem mn = true)
    (hd : OpResolves F W Q d) (hs : OpResolves F W Q s)
    (hds : (encMemName d && encMemName s) = false) :
    encodableLinstrR F W (.Lopn [.reg d] mn [.reg s]) Q = true :=
  (encodableLinstrR_mov_iff hm).2 (encTwoAddr_ne_nil hd hs hds)

/-- An encodable register move has resolving names. -/
theorem opResolves_of_encodableLinstrR_mov {F W Q : Nat} {mn d s : String}
    (hm : isMovMnem mn = true) (h : encodableLinstrR F W (.Lopn [.reg d] mn [.reg s]) Q = true) :
    OpResolves F W Q d ∧ OpResolves F W Q s :=
  opResolves_of_encTwoAddr ((encodableLinstrR_mov_iff hm).1 h)

/-- A move between an allocated operand and a general-purpose register is encodable,
    in either direction. -/
theorem encodableLinstrR_mov_gp_left {F W Q : Nat} {mn r n : String} (hm : isMovMnem mn = true)
    (hr : isGpName r = true) (hn : AllocOp F W Q (.reg n)) :
    encodableLinstrR F W (.Lopn [.reg r] mn [.reg n]) Q = true :=
  encodableLinstrR_mov hm (opResolves_of_isGpName hr) hn.opResolves
    (by simp [encMemName_of_isGpName hr])

theorem encodableLinstrR_mov_gp_right {F W Q : Nat} {mn r n : String} (hm : isMovMnem mn = true)
    (hr : isGpName r = true) (hn : AllocOp F W Q (.reg n)) :
    encodableLinstrR F W (.Lopn [.reg n] mn [.reg r]) Q = true :=
  encodableLinstrR_mov hm hn.opResolves (opResolves_of_isGpName hr)
    (by simp [encMemName_of_isGpName hr])

/-! ## The scratch select -/

theorem carriesNoBytes_cmov64 (dn cn tn fn : String) :
    carriesNoBytes (.Lopn [.reg dn] "CMOV:64" [.reg cn, .reg tn, .reg fn]) = false := by
  simp [carriesNoBytes, show isMulHiBinding "CMOV:64" = false from by decide +kernel,
    show ("CMOV:64" == "KEEP") = false from by decide +kernel]

/-- A select over four general-purpose registers is encodable. -/
theorem encodableLinstrR_cmov64_gp {F W Q : Nat} {dn cn tn fn : String}
    (hd : isGpName dn = true) (hc : isGpName cn = true) (ht : isGpName tn = true)
    (hf : isGpName fn = true) :
    encodableLinstrR F W (.Lopn [.reg dn] "CMOV:64" [.reg cn, .reg tn, .reg fn]) Q = true := by
  have he := GatherFullBody.encodeLopn_cmov64_emits F W dn cn tn fn Q (by simp [hd, hc, ht, hf])
  simp [encodableLinstrR, encodeLinstrR, he, carriesNoBytes_cmov64,
    encCmovSelect_ne_nil]

theorem isGpName_of_allocOp_not_spill {F W Q : Nat} {n : String} (h : AllocOp F W Q (.reg n))
    (hs : (LOperand.reg n).isSpill = false) : isGpName n = true := by
  obtain ⟨m, hm, hc⟩ := h
  simp only [LOperand.reg.injEq] at hm
  subst hm
  rcases hc with hg | ⟨hk, _⟩
  · exact hg
  · rw [isSpill_reg, hk] at hs; cases hs

/-! ## The scratch comparison -/

/-- The materialised comparisons the encoder builds: `SETE` and `SETNE`, untagged or
    at the `:64` tag. -/
def isSetccEncMnem (opn : String) : Bool :=
  opn == "SETE" || opn == "SETNE" || opn == "SETE:64" || opn == "SETNE:64"

/-- The materialised-comparison dispatch: a mnemonic whose base is in none of the
    tables before the comparison arm reaches `encSetccCmp`. -/
theorem dispatch_setcc (frame spillW op : Nat) (mnem base : String) (dn an sn : String)
    (qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none) (htag : tagShiftExt base = none)
    (halu : aluOpcode base = none) (h0f : twoByteOpcode base = none)
    (hst : (base == "STOREIDX") = false) (hcmp : (base == "CMP") = false)
    (hsh : (base == "SHL" || base == "SHR" || base == "SAR") = false)
    (hcc : setccCmpOp base = some op)
    (hgp : (isGpName dn && isGpName an && isGpName sn) = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg an, .reg sn]) qsaveB
      = encSetccCmp (rexW (mnemWidth mnem)) op (gpNumU dn) (gpNumU an) (gpNumU sn) := by
  simp only [Bool.or_eq_false_iff] at hsh
  obtain ⟨⟨hshl, hshr⟩, hsar⟩ := hsh
  simp only [encodeLopn, hbind, hstrip, hmulx, hmulxmem, hadx, htag, halu, h0f, hst, hcmp,
    hshl, hshr, hsar, hcc, hgp, Bool.or_false, Bool.false_eq_true, if_false, if_true]

theorem encodeLopn_setcc_ne_nil {F W Q : Nat} {opn dn an sn : String}
    (ho : isSetccEncMnem opn = true)
    (hd : isGpName dn = true) (ha : isGpName an = true) (hs : isGpName sn = true) :
    encodeLopn F W (.Lopn [.reg dn] opn [.reg an, .reg sn]) Q ≠ [] := by
  have hgp : (isGpName dn && isGpName an && isGpName sn) = true := by simp [hd, ha, hs]
  simp only [isSetccEncMnem, Bool.or_eq_true, beq_iff_eq] at ho
  rcases ho with ((rfl | rfl) | rfl) | rfl
  · rw [dispatch_setcc F W 0x94 "SETE" "SETE" dn an sn Q (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hgp]
    exact encSetccCmp_ne_nil _ _ _ _ _
  · rw [dispatch_setcc F W 0x95 "SETNE" "SETNE" dn an sn Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hgp]
    exact encSetccCmp_ne_nil _ _ _ _ _
  · rw [dispatch_setcc F W 0x94 "SETE:64" "SETE" dn an sn Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hgp]
    exact encSetccCmp_ne_nil _ _ _ _ _
  · rw [dispatch_setcc F W 0x95 "SETNE:64" "SETNE" dn an sn Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hgp]
    exact encSetccCmp_ne_nil _ _ _ _ _

/-- A materialised comparison `SETE`/`SETNE` over three general-purpose registers is
    encodable. -/
theorem encodableLinstrR_setcc_gp {F W Q : Nat} {opn dn an sn : String}
    (ho : isSetccEncMnem opn = true)
    (hd : isGpName dn = true) (ha : isGpName an = true) (hs : isGpName sn = true) :
    encodableLinstrR F W (.Lopn [.reg dn] opn [.reg an, .reg sn]) Q = true := by
  have he := encodeLopn_setcc_ne_nil (F := F) (W := W) (Q := Q) ho hd ha hs
  simp [encodableLinstrR, encodeLinstrR, he]

/-- The materialised comparisons against an immediate the encoder builds: a mnemonic of
    `isSetccEncMnem` and an immediate that is not a 64-bit immediate at or above `2^31`,
    which `LprogAsmPrinter.renderSetcc` declines. -/
def isSetccImmEnc (opn : String) (v : Nat) : Bool :=
  isSetccEncMnem opn && !(rexW (mnemWidth opn) == 1 && decide (2 ^ 31 ≤ v))

/-- The immediate materialised-comparison dispatch: on `Lopn [.reg dn] mnem [.reg an, .imm v]`
    with base `SETE` or `SETNE`, two general-purpose registers and an immediate the printer
    renders, `encodeLopn` reaches `encSetccCmpImm`. -/
theorem dispatch_setccImm (frame spillW : Nat) (mnem base : String) (dn an : String)
    (v qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none)
    (hcc : (base == "SETE" || base == "SETNE") = true)
    (hok : (isGpName dn && isGpName an && !(rexW (mnemWidth mnem) == 1 && decide (2 ^ 31 ≤ v)))
      = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg an, .imm v]) qsaveB
      = encSetccCmpImm (rexW (mnemWidth mnem)) ((setccCmpOp base).getD 0x94) (gpNumU dn)
          (gpNumU an) v := by
  simp only [encodeLopn, hbind, hstrip, hmulx, hmulxmem, hadx, hcc, hok,
    Bool.false_eq_true, if_false, if_true]

theorem encodeLopn_setccImm_ne_nil {F W Q : Nat} {opn dn an : String} {v : Nat}
    (ho : isSetccImmEnc opn v = true) (hd : isGpName dn = true) (ha : isGpName an = true) :
    encodeLopn F W (.Lopn [.reg dn] opn [.reg an, .imm v]) Q ≠ [] := by
  simp only [isSetccImmEnc, Bool.and_eq_true] at ho
  obtain ⟨hm, hv⟩ := ho
  have hok : (isGpName dn && isGpName an && !(rexW (mnemWidth opn) == 1 && decide (2 ^ 31 ≤ v)))
      = true := by rw [hd, ha, hv]; rfl
  simp only [isSetccEncMnem, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with ((rfl | rfl) | rfl) | rfl
  · rw [dispatch_setccImm F W "SETE" "SETE" dn an v Q (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hok]
    exact encSetccCmpImm_ne_nil _ _ _ _ _
  · rw [dispatch_setccImm F W "SETNE" "SETNE" dn an v Q (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hok]
    exact encSetccCmpImm_ne_nil _ _ _ _ _
  · rw [dispatch_setccImm F W "SETE:64" "SETE" dn an v Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hok]
    exact encSetccCmpImm_ne_nil _ _ _ _ _
  · rw [dispatch_setccImm F W "SETNE:64" "SETNE" dn an v Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hok]
    exact encSetccCmpImm_ne_nil _ _ _ _ _

/-- A materialised comparison `SETE`/`SETNE` of a general-purpose register against an
    immediate the printer renders, into a general-purpose register, is encodable. -/
theorem encodableLinstrR_setccImm_gp {F W Q : Nat} {opn dn an : String} {v : Nat}
    (ho : isSetccImmEnc opn v = true) (hd : isGpName dn = true) (ha : isGpName an = true) :
    encodableLinstrR F W (.Lopn [.reg dn] opn [.reg an, .imm v]) Q = true := by
  have he := encodeLopn_setccImm_ne_nil (F := F) (W := W) (Q := Q) ho hd ha
  simp [encodableLinstrR, encodeLinstrR, he]

/-! ## The lowering families

The deciders of the instruction families the lowering emits beyond the register moves, the
select and the materialised comparisons, each with the encodability of its forms over
general-purpose registers. Every decider reads the mnemonic through `stripWidthTag`, as
`encodeLopn` does. -/

/-- The two-address operations over two registers the encoder builds: the bases `ADD`,
    `SUB`, `AND`, `OR`, `XOR` (group-1 opcodes), `MUL` (`IMUL`, `0F AF`) and `CMP`. -/
def x86Alu (opn : String) : Bool :=
  ["ADD", "SUB", "AND", "OR", "XOR", "MUL", "CMP"].contains (stripWidthTag opn)

/-- The two-address operations against an immediate the encoder builds: an operation of
    `x86Alu` whose immediate denotes itself through the `imm32` field at the width of the
    mnemonic (`imm32Fits`), and the shifts `SHL`, `SHR`, `SAR` by any immediate. -/
def x86AluImm (opn : String) (v : Nat) : Bool :=
  (x86Alu opn && imm32Fits (rexW (mnemWidth opn)) v) ||
    ["SHL", "SHR", "SAR"].contains (stripWidthTag opn)

/-- The three-register shifts the encoder builds: `SHL`, `SHR` and `SAR` at the 64-bit width
    (the BMI2 `shlx`/`shrx`/`sarx`). -/
def x86ShiftReg (opn : String) : Bool :=
  ["SHL", "SHR", "SAR"].contains (stripWidthTag opn) && mnemWidth opn == 64

/-- The one-source register operations the encoder builds: the count-in-tag shifts
    `SHL:n`, `SHR:n`, `SAR:n`, the negation `NEG` at the 64-bit width, and the width casts
    `CASTW_*` of `castMovBits`. -/
def x86Unary (opn : String) : Bool :=
  (tagShiftExt (stripWidthTag opn)).isSome || (stripWidthTag opn == "NEG" && mnemWidth opn == 64)
    || (castMovBits (stripWidthTag opn)).isSome

/-- The one-source loads and stores the encoder builds through the two-address form: the
    bases `LOAD` and `STORE`. -/
def x86MemMov (mn : String) : Bool := ["LOAD", "STORE"].contains (stripWidthTag mn)

/-- The strides x86 SIB addressing encodes. -/
def x86SibScale (sc : Nat) : Bool := [1, 2, 4, 8].contains sc

/-- The register-indexed loads and address computations the encoder builds: `LOADIDX` at a
    stride of `x86SibScale`, and `LEA` at such a stride with an index other than `RSP`. -/
def x86SibLoad (opn xn : String) (sc : Nat) : Bool :=
  x86SibScale sc && (stripWidthTag opn == "LOADIDX" || (stripWidthTag opn == "LEA" && gpNumU xn != 4))

/-- The register-indexed stores the encoder builds: `STOREIDX` at a stride of
    `x86SibScale`. -/
def x86SibStore (opn : String) (sc : Nat) : Bool :=
  stripWidthTag opn == "STOREIDX" && x86SibScale sc

/-- The three-source carry-chain additions the encoder builds over registers: `ADCX` (the
    `ADOX` form with a value carry-in has no encoding). -/
def x86Carry3 (opn : String) : Bool := stripWidthTag opn == "ADCX"

/-- The flag materialisations the encoder builds into a register: the carry-out bindings
    `ADCXHI`/`ADOXHI` over any sources, and `SETC` without sources. -/
def x86FlagOut (opn : String) (srcs : List LOperand) : Bool :=
  isCarryOutBinding opn || (stripWidthTag opn == "SETC" && srcs.isEmpty)

/-- The widening multiplications the encoder builds into two registers: `MULX`. -/
def x86WideMul (opn : String) : Bool := stripWidthTag opn == "MULX"

/-- The element indices of the constant-index stack-array store the encoder builds: those
    whose byte offset `stackDispOk` admits. -/
def x86StoreImm (k : Nat) : Bool := stackDispOk k

/-- The stack-array zeroings the encoder builds: a positive count of 64-bit words whose last
    byte offset `stackDispOk` admits. -/
def x86ZeroArr (n w : Nat) : Bool := w == 64 && decide (0 < n) && stackDispOk (n - 1)

/-- The immediates the encoder moves into a spill slot under a move mnemonic: an immediate
    that fits the sign-extended `imm32` field, or any immediate at the 64-bit width. -/
def x86SlotImm (mn : String) (v : Nat) : Bool :=
  v < 2 ^ 31 || 2 ^ 64 - 2 ^ 31 ≤ v || mnemWidth mn == 64

/-- The instructions the encoder accepts whatever their operands: the forms without bytes
    (`carriesNoBytes`) and the control transfers `Lgoto`, `Lcall` and `Lcond` on a named
    condition. -/
def x86Fixed : LinstrR → Bool
  | .Lgoto _ => true
  | .Lcall _ _ => true
  | .Lcond (.reg _) _ => true
  | i => carriesNoBytes i

/-- A mnemonic whose base has a count-in-tag shift extension is not one of the bases the
    dispatch of `encodeLopn` tests before the count-in-tag arm. -/
theorem stripWidthTag_ne_of_tagShift {opn : String} {ext : Nat}
    (hs : tagShiftExt (stripWidthTag opn) = some ext) {x : String} (hx : tagShiftExt x = none) :
    stripWidthTag opn ≠ x := by
  intro he
  rw [he, hx] at hs
  cases hs

theorem encodable_of_ne_nil {F W Q : Nat} {i : LinstrR}
    (h : encodeLinstrR F W (fun _ => 0) i Q ≠ []) : encodableLinstrR F W i Q = true := by
  simp [encodableLinstrR, h]

theorem encodable_lopn_of_ne_nil {F W Q : Nat} {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} (h : encodeLopn F W (.Lopn dsts opn srcs) Q ≠ []) :
    encodableLinstrR F W (.Lopn dsts opn srcs) Q = true :=
  encodable_of_ne_nil (by simpa [encodeLinstrR] using h)

theorem mem_of_contains {l : List String} {x : String} (h : l.contains x = true) : x ∈ l := by
  simpa using h

theorem encTagShift_ne_nil (w ext dn : Nat) (base : String) : encTagShift w ext dn base ≠ [] := by
  unfold encTagShift
  dsimp only
  split <;> simp [encShift1, encShiftImmw]

theorem stripWidthTag_MOV : stripWidthTag "MOV" = "MOV" := by decide +kernel
theorem stripWidthTag_MOV64 : stripWidthTag "MOV:64" = "MOV" := by decide +kernel
theorem stripWidthTag_MOVQ : stripWidthTag "MOVQ" = "MOVQ" := by decide +kernel
theorem mnemWidth_MOV : mnemWidth "MOV" = 32 := by decide +kernel
theorem mnemWidth_MOV64 : mnemWidth "MOV:64" = 64 := by decide +kernel
theorem mnemWidth_MOVQ : mnemWidth "MOVQ" = 64 := by decide +kernel

/-- A base of `castMovBits` is one of the eight width casts. -/
theorem mem_of_castMovBits {b : String} {m : Nat} (h : castMovBits b = some m) :
    b ∈ ["CASTW_64_16", "CASTW_16_64", "CASTW_16_16", "CASTW_16_32", "CASTW_32_16",
      "CASTW_64_32", "CASTW_32_64", "CASTW_32_32"] := by
  unfold castMovBits at h
  split at h
  · rename_i h1
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with (((h | h) | h) | h) | h <;> simp [h]
  · split at h
    · rename_i h2
      simp only [Bool.or_eq_true, beq_iff_eq] at h2
      rcases h2 with (h | h) | h <;> simp [h]
    · cases h

/-- The dispatch facts of a mnemonic whose base is a literal that is none of the bases
    tested before the operand-shape arms of `encodeLopn`. -/
theorem dispatch_facts {opn base : String} (hs : stripWidthTag opn = base)
    (h1 : (base == "ADCXHI" || base == "ADOXHI") = false) (h2 : (base == "MULXHI") = false) :
    (isCarryOutBinding opn || isMulHiBinding opn) = false := by
  simp only [isCarryOutBinding, isMulHiBinding, hs, h1, h2, Bool.or_false]

/-- **A move of an immediate into a general-purpose register is encodable.** -/
theorem encodableLinstrR_movImm_gp {F W Q : Nat} {mn dn : String} {v : Nat}
    (hm : isMovMnem mn = true) (hd : isGpName dn = true) :
    encodableLinstrR F W (.Lopn [.reg dn] mn [.imm v]) Q = true := by
  apply encodable_lopn_of_ne_nil
  have hq := (notSlotMem_of_isGpName hd).1
  simp only [isMovMnem, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with (rfl | rfl) | rfl <;>
    simp [encodeLopn, isCarryOutBinding, isMulHiBinding, adxPrefix, encImmOp, hq,
      stripWidthTag_MOV, stripWidthTag_MOV64] <;>
    split_ifs <;> simp [encMovImmw, ScalarEncoder.encMovImm64] <;> split <;> simp

/-- **A move of an immediate into a spill slot with a frame offset is encodable** when the
    immediate fits the sign-extended `imm32` field or the move is 64-bit. -/
theorem encodableLinstrR_movImm_slot {F W Q : Nat} {mn dn : String} {v : Nat}
    (hm : isMovMnem mn = true) (hd : (spillQsaveOff F W dn Q).isSome = true)
    (hv : x86SlotImm mn v = true) :
    encodableLinstrR F W (.Lopn [.reg dn] mn [.imm v]) Q = true := by
  apply encodable_lopn_of_ne_nil
  obtain ⟨off, ho⟩ := Option.isSome_iff_exists.1 hd
  have hq := isSpillOrQsave_of_spillQsaveOff ho
  have hg := isGpName_of_spillQsaveOff ho
  have hmr : ∀ o : Int, encMovImmRspMem 1 o v ≠ [] ∧ encMovImmRspMem 0 o v ≠ [] := by
    intro o
    constructor <;> (unfold encMovImmRspMem; split_ifs <;> simp)
  simp only [x86SlotImm, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
  simp only [isMovMnem, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with (rfl | rfl) | rfl <;>
    simp only [encodeLopn, isCarryOutBinding, isMulHiBinding, stripWidthTag_MOV,
      stripWidthTag_MOV64, stripWidthTag_MOVQ, hq, ho] <;>
    simp (config := { decide := true }) only [if_false, if_true, adxPrefix] <;>
    split_ifs <;> simp_all [rexW, mnemWidth_MOV, mnemWidth_MOV64, mnemWidth_MOVQ,
      encRspMem_ne_nil]

/-- **A two-address operation of `x86Alu` over two general-purpose registers is
    encodable.** -/
theorem encodableLinstrR_alu {F W Q : Nat} {opn dn sn : String} (ho : x86Alu opn = true)
    (hd : isGpName dn = true) (hs : isGpName sn = true) :
    encodableLinstrR F W (.Lopn [.reg dn] opn [.reg dn, .reg sn]) Q = true := by
  apply encodable_lopn_of_ne_nil
  have hq := notSlotMem_of_isGpName hd
  have hq' := notSlotMem_of_isGpName hs
  have hm := mem_of_contains ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h <;>
    simp [encodeLopn, isCarryOutBinding, isMulHiBinding, h, adxPrefix, tagShiftExt, aluOpcode,
      twoByteOpcode, encTwoAddr, spillQsaveOff_of_not hq.1, spillQsaveOff_of_not hq'.1,
      parseMemNameGp_eq_none hq.2, parseMemNameGp_eq_none hq'.2, hd, hs, encAluRRw, enc0FRRw]

/-- **A two-address operation of `x86AluImm` against an immediate over a general-purpose
    register is encodable.** -/
theorem encodableLinstrR_aluImm {F W Q : Nat} {opn dn : String} {v : Nat}
    (ho : x86AluImm opn v = true) (hd : isGpName dn = true) :
    encodableLinstrR F W (.Lopn [.reg dn] opn [.reg dn, .imm v]) Q = true := by
  apply encodable_lopn_of_ne_nil
  have hq := (notSlotMem_of_isGpName hd).1
  simp only [x86AluImm, Bool.or_eq_true, Bool.and_eq_true] at ho
  rcases ho with ⟨ho, hv⟩ | ho
  · have hm := mem_of_contains ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h <;>
      simp [encodeLopn, isCarryOutBinding, isMulHiBinding, h, adxPrefix, encImmOp, hq,
        shiftImmExt, aluImmDigit, hv] <;>
      split_ifs <;> simp [encAluImm8, encAluImmw, encImulImm8w, encImulImm32w]
  · have hm := mem_of_contains ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h <;>
      simp [encodeLopn, isCarryOutBinding, isMulHiBinding, h, adxPrefix, encImmOp, hq,
        shiftImmExt] <;>
      split_ifs <;> simp [encShift1, encShiftImmw]

/-- **A three-register shift of `x86ShiftReg` over general-purpose registers is
    encodable.** -/
theorem encodableLinstrR_shiftReg {F W Q : Nat} {opn dn an sn : String}
    (ho : x86ShiftReg opn = true) (hd : isGpName dn = true) (ha : isGpName an = true)
    (hs : isGpName sn = true) :
    encodableLinstrR F W (.Lopn [.reg dn] opn [.reg an, .reg sn]) Q = true := by
  apply encodable_lopn_of_ne_nil
  simp only [x86ShiftReg, Bool.and_eq_true, beq_iff_eq] at ho
  obtain ⟨ho, hw⟩ := ho
  have hm := mem_of_contains ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h <;>
    simp [encodeLopn, isCarryOutBinding, isMulHiBinding, h, adxPrefix, tagShiftExt, aluOpcode,
      twoByteOpcode, rexW, hw, hd, ha, hs, ScalarEncoder.encShiftX,
      ScalarEncoder.encVex3RR]

/-- **A one-source register operation of `x86Unary` over general-purpose registers is
    encodable.** -/
theorem encodableLinstrR_unary {F W Q : Nat} {opn dn sn : String} (ho : x86Unary opn = true)
    (hd : isGpName dn = true) (hs : isGpName sn = true) :
    encodableLinstrR F W (.Lopn [.reg dn] opn [.reg sn]) Q = true := by
  simp only [x86Unary, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists]
    at ho
  rcases ho with (⟨ext, he⟩ | ⟨hn, hw⟩) | ⟨m, hm⟩
  · have hco : isCarryOutBinding opn = false := by
      simp only [isCarryOutBinding, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      exact ⟨stripWidthTag_ne_of_tagShift he (by decide +kernel),
        stripWidthTag_ne_of_tagShift he (by decide +kernel)⟩
    have hmh : isMulHiBinding opn = false := by
      simp only [isMulHiBinding, beq_eq_false_iff_ne]
      exact stripWidthTag_ne_of_tagShift he (by decide +kernel)
    have hmx : (stripWidthTag opn == "MULX") = false := by
      simpa using stripWidthTag_ne_of_tagShift he (x := "MULX") (by decide +kernel)
    have hmm : (stripWidthTag opn == "MULXMEM") = false := by
      simpa using stripWidthTag_ne_of_tagShift he (x := "MULXMEM") (by decide +kernel)
    have hadx : adxPrefix (stripWidthTag opn) = none := by
      cases hp : adxPrefix (stripWidthTag opn) with
      | none => rfl
      | some p =>
        exfalso
        unfold adxPrefix at hp
        split at hp
        · exact stripWidthTag_ne_of_tagShift he (x := "ADCX") (by decide +kernel) ‹_›
        · exact stripWidthTag_ne_of_tagShift he (x := "ADOX") (by decide +kernel) ‹_›
        · cases hp
    have henc : encodeLopn F W (.Lopn [.reg dn] opn [.reg sn]) Q
        = (if tagShiftCount (stripWidthTag opn) = 0 then
             (if dn = sn then [] else encAluRRw (rexW (mnemWidth opn)) 0x89 (gpNumU dn)
               (gpNumU sn))
           else (if dn = sn then [] else encAluRRw (rexW (mnemWidth opn)) 0x89 (gpNumU dn)
               (gpNumU sn)) ++ encTagShift (rexW (mnemWidth opn)) ext (gpNumU dn)
                 (stripWidthTag opn)) := by
      simp [encodeLopn, hco, hmh, hmx, hmm, hadx, he, hd, hs]
    by_cases hn : tagShiftCount (stripWidthTag opn) = 0
    · by_cases hds : dn = sn
      · subst hds
        have hid : isIdentityTagShift opn = true := by
          simp [isIdentityTagShift, hco, he, hn]
        simp [encodableLinstrR, carriesNoBytes, hmh, hd, hid]
      · apply encodable_lopn_of_ne_nil
        rw [henc]
        simp [hn, hds, encAluRRw]
    · apply encodable_lopn_of_ne_nil
      rw [henc]
      simp [hn, encTagShift_ne_nil]
  · apply encodable_lopn_of_ne_nil
    simp [encodeLopn, isCarryOutBinding, isMulHiBinding, hn, adxPrefix, tagShiftExt, aluOpcode,
      twoByteOpcode, hw, rexW, hd, hs, ScalarEncoder.encUnaryF7]
  · apply encodable_lopn_of_ne_nil
    have hmem := mem_of_castMovBits hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h | h | h | h <;>
      simp [encodeLopn, isCarryOutBinding, isMulHiBinding, h, adxPrefix, tagShiftExt,
        aluOpcode, twoByteOpcode, castMovBits, hd, hs, encCastW, encMovzx16RR, encMov32RR]

/-- **A load or store of `x86MemMov` between resolving names, at most one of them a memory
    name, is encodable.** -/
theorem encodableLinstrR_memMov {F W Q : Nat} {mn d s : String} (hm : x86MemMov mn = true)
    (hd : OpResolves F W Q d) (hs : OpResolves F W Q s)
    (hds : (encMemName d && encMemName s) = false) :
    encodableLinstrR F W (.Lopn [.reg d] mn [.reg s]) Q = true := by
  apply encodable_lopn_of_ne_nil
  have hm' := mem_of_contains hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
  rcases hm' with h1 | h1
  · rw [dispatch_alu_one_w F W 0x8b mn "LOAD" d s Q
      (by simp [isCarryOutBinding, isMulHiBinding, h1]) h1 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    exact encTwoAddr_ne_nil hd hs hds
  · rw [dispatch_alu_one_w F W 0x89 mn "STORE" d s Q
      (by simp [isCarryOutBinding, isMulHiBinding, h1]) h1 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    exact encTwoAddr_ne_nil hd hs hds

theorem x86SibScale_cases {sc : Nat} (h : x86SibScale sc = true) :
    sc = 1 ∨ sc = 2 ∨ sc = 4 ∨ sc = 8 := by
  simpa [x86SibScale] using h

/-- **A register-indexed load or address computation of `x86SibLoad` over general-purpose
    registers is encodable.** -/
theorem encodableLinstrR_sibLoad {F W Q : Nat} {opn dn bn xn : String} {sc : Nat}
    (ho : x86SibLoad opn xn sc = true) (hd : isGpName dn = true) (hb : isGpName bn = true)
    (hx : isGpName xn = true) :
    encodableLinstrR F W (.Lopn [.reg dn] opn [.arrIdx bn xn sc]) Q = true := by
  apply encodable_lopn_of_ne_nil
  simp only [x86SibLoad, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq] at ho
  obtain ⟨hsc, h1 | ⟨h1, h4⟩⟩ := ho
  · rcases x86SibScale_cases hsc with rfl | rfl | rfl | rfl <;>
      simp [encodeLopn, isCarryOutBinding, isMulHiBinding, h1, adxPrefix, tagShiftExt,
        aluOpcode, twoByteOpcode, encLoadIdx, encMemMovSibw, enc0FMemSibw, hd, hb, hx]
  · rcases x86SibScale_cases hsc with rfl | rfl | rfl | rfl <;>
      simp [encodeLopn, isCarryOutBinding, isMulHiBinding, h1, adxPrefix, tagShiftExt,
        aluOpcode, twoByteOpcode, encMemMovSibw, hd, hb, hx, h4]

/-- **A register-indexed store of `x86SibStore` over general-purpose registers is
    encodable**, whatever its array destination. -/
theorem encodableLinstrR_sibStore {F W Q : Nat} {a : LOperand} {opn bn xn vn : String}
    {sc : Nat} (ho : x86SibStore opn sc = true) (hb : isGpName bn = true)
    (hx : isGpName xn = true) (hv : isGpName vn = true) :
    encodableLinstrR F W (.Lopn [a] opn [.arrIdx bn xn sc, .reg vn]) Q = true := by
  apply encodable_lopn_of_ne_nil
  simp only [x86SibStore, Bool.and_eq_true, beq_iff_eq] at ho
  obtain ⟨h1, hsc⟩ := ho
  rcases x86SibScale_cases hsc with rfl | rfl | rfl | rfl <;>
    cases a <;>
    simp [encodeLopn, isCarryOutBinding, isMulHiBinding, h1, adxPrefix, tagShiftExt, aluOpcode,
      twoByteOpcode, encStoreIdx, encMemMovSibw, encMovwSib, encMovbSib, hb, hx, hv]

/-- **A three-source carry-chain addition of `x86Carry3` over general-purpose registers is
    encodable.** -/
theorem encodableLinstrR_carry3 {F W Q : Nat} {opn dn an sn kn : String}
    (ho : x86Carry3 opn = true) (hd : isGpName dn = true) (ha : isGpName an = true)
    (hs : isGpName sn = true) (hk : isGpName kn = true) :
    encodableLinstrR F W (.Lopn [.reg dn] opn [.reg an, .reg sn, .reg kn]) Q = true := by
  apply encodable_lopn_of_ne_nil
  simp only [x86Carry3, beq_iff_eq] at ho
  have h1 := notSlotMem_of_isGpName hd
  have h2 := notSlotMem_of_isGpName ha
  have h3 := notSlotMem_of_isGpName hs
  have h4 := notSlotMem_of_isGpName hk
  by_cases han : an = dn <;>
    simp [encodeLopn, isCarryOutBinding, isMulHiBinding, ho, adxPrefix, h1.1, h1.2, h2.1, h2.2,
      h3.1, h3.2, h4.1, h4.2, encBtImm, han]

/-- **A flag materialisation of `x86FlagOut` into a general-purpose register is
    encodable.** -/
theorem encodableLinstrR_flagOut {F W Q : Nat} {opn dn : String} {srcs : List LOperand}
    (ho : x86FlagOut opn srcs = true) (hd : isGpName dn = true) :
    encodableLinstrR F W (.Lopn [.reg dn] opn srcs) Q = true := by
  apply encodable_lopn_of_ne_nil
  simp only [x86FlagOut, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    List.isEmpty_iff] at ho
  rcases ho with ho | ⟨h1, rfl⟩
  · simp [encodeLopn, ho, hd, encSetccMovzx]
  · have hco : isCarryOutBinding opn = false := by simp [isCarryOutBinding, h1]
    simp [encodeLopn, hco, isMulHiBinding, adxPrefix, h1, encSetccMovzx]

/-- **A widening multiplication of `x86WideMul` into two general-purpose registers, from a
    general-purpose register, is encodable.** -/
theorem encodableLinstrR_wideMul {F W Q : Nat} {opn ln hn sn : String}
    (ho : x86WideMul opn = true) (hl : isGpName ln = true) (hh : isGpName hn = true)
    (hs : isGpName sn = true) :
    encodableLinstrR F W (.Lopn [.reg ln, .reg hn] opn [.reg sn]) Q = true := by
  apply encodable_lopn_of_ne_nil
  simp only [x86WideMul, beq_iff_eq] at ho
  have hl' := notSlotMem_of_isGpName hl
  have hh' := notSlotMem_of_isGpName hh
  have hs' := notSlotMem_of_isGpName hs
  simp [encodeLopn, isCarryOutBinding, isMulHiBinding, ho, hl'.1, hl'.2, hh'.1, hh'.2, hs'.1,
    hs'.2, mulxSrcMem?_of_isGpName F W Q hs]
  split_ifs <;> simp [encMulxSameDst, ScalarEncoder.encMulxRR, encRspMem]

/-- **An instruction of `x86Fixed` is encodable.** -/
theorem encodableLinstrR_fixed {F W Q : Nat} {i : LinstrR} (hi : x86Fixed i = true) :
    encodableLinstrR F W i Q = true := by
  unfold x86Fixed at hi
  split at hi
  · apply encodable_of_ne_nil
    simp only [encodeLinstrR]
    split_ifs <;> simp [encJmp8, encJmp32]
  · apply encodable_of_ne_nil
    simp [encodeLinstrR, encCall32]
  · apply encodable_of_ne_nil
    simp only [encodeLinstrR]
    split_ifs <;> simp [encJcc8, encJcc32]
  · simp [encodableLinstrR, hi]

/-- **A constant-index stack-array store of `x86StoreImm` over a general-purpose base and
    value is encodable**, whatever its array destination. -/
theorem encodableLinstrR_storeImm {F W Q : Nat} {a : LOperand} {bn vn : String} {k : Nat}
    (hk : x86StoreImm k = true) (hb : isGpName bn = true) (hv : isGpName vn = true) :
    encodableLinstrR F W (.Lopn [a] "STOREIMM" [.reg bn, .reg vn, .imm k]) Q = true := by
  apply encodable_lopn_of_ne_nil
  rw [encodeLopn_storeImm F W a bn vn k Q hb hv hk]
  simp [encMemMovw]

/-- **A stack-array zeroing of `x86ZeroArr` into a general-purpose register is
    encodable.** -/
theorem encodableLinstrR_zeroArr {F W Q : Nat} {dn : String} {n w : Nat}
    (ho : x86ZeroArr n w = true) (hd : isGpName dn = true) :
    encodableLinstrR F W (.Lopn [.reg dn] "ZEROARR" [.imm n, .imm w]) Q = true := by
  simp only [x86ZeroArr, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
  obtain ⟨⟨rfl, hn⟩, hk⟩ := ho
  apply encodable_lopn_of_ne_nil
  rw [encodeLopn_zeroArr F W dn n Q hd hn hk]
  exact encZeroArr_ne_nil _ hn

/-- **A stack-array zeroing of `x86ZeroArr` from a general-purpose base register is
    encodable.** -/
theorem encodableLinstrR_zeroArrSrc {F W Q : Nat} {bn : String} {n w : Nat}
    (ho : x86ZeroArr n w = true) (hb : isGpName bn = true) :
    encodableLinstrR F W (.Lopn [] "ZEROARR" [.reg bn, .imm n, .imm w]) Q = true := by
  simp only [x86ZeroArr, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
  obtain ⟨⟨rfl, hn⟩, hk⟩ := ho
  apply encodable_lopn_of_ne_nil
  rw [encodeLopn_zeroArrSrc F W bn n Q hb hn hk]
  exact encZeroArr_ne_nil _ hn

/-! ## Load forwarding -/

section LoadCSE

open CatCrypt.Crypto.Optimizer.LoadCSE

/-- A memory name of the encoder is a memory name of the load forwarding. -/
theorem isMemName_of_encMemName {n : String} (h : encMemName n = true) : isMemName n = true := by
  simp only [encMemName, Bool.or_eq_true, Option.isSome_iff_exists] at h
  simp only [isMemName, Bool.or_eq_true, PhysAbiShape.isPrefixOf_eq_list]
  rcases h with hq | ⟨p, hp⟩
  · simp only [isSpillOrQsave, hasPrefix, Bool.or_eq_true] at hq
    rcases hq with hk | hq
    · exact Or.inl (Or.inl hk)
    · exact Or.inl (Or.inr hq)
  · exact Or.inr (hasPrefix_mem_of_parseMemName hp)

/-- The load environment holds only names that resolve. -/
def EnvResolves (F W Q : Nat) (h : LoadEnv) : Prop := ∀ p ∈ h, OpResolves F W Q p.2

end LoadCSE

/-! ## The x86 encoder -/

/-- **The x86 encoder**: the context of a body is its frame size, spill width and save
    block; an instruction is encodable in a context when `encodableLinstrR` holds there;
    the encoder registers are the general-purpose registers; a name resolves when
    `OpResolves` holds; a spill slot has a frame offset when `spillQsaveOff` parses; the
    memory names are `encMemName`; the materialised comparisons are `isSetccEncMnem` against
    a register and `isSetccImmEnc` against an immediate; the further families are decided by
    `x86SlotImm`, `x86Alu`, `x86AluImm`, `x86ShiftReg`, `x86Unary`, `x86MemMov`,
    `x86SibLoad`, `x86SibStore`, `x86Carry3`, `x86FlagOut`, `x86WideMul`, `x86StoreImm`,
    `x86ZeroArr` and `x86Fixed`. -/
def x86Enc : IsaEncoder where
  Ctx := Nat × Nat × Nat
  ctx body := (frameSize body, if bodyIsU64 body then 64 else 32, qsaveBytesFor body)
  instr c i := encodableLinstrR c.1 c.2.1 i c.2.2
  reg := isGpName
  resolves c n := OpResolves c.1 c.2.1 c.2.2 n
  slot c n := (spillQsaveOff c.1 c.2.1 n c.2.2).isSome = true
  memName := encMemName
  setcc := isSetccEncMnem
  setccImm := isSetccImmEnc
  slotImm := x86SlotImm
  alu := x86Alu
  aluImm := x86AluImm
  shiftReg := x86ShiftReg
  unary := x86Unary
  memMov := x86MemMov
  sibLoad := x86SibLoad
  sibStore := x86SibStore
  carry3 := x86Carry3
  flagOut := x86FlagOut
  wideMul := x86WideMul
  storeImm := x86StoreImm
  zeroArr := x86ZeroArr
  fixed := x86Fixed

/-- The decision of `OpResolves` at a frame size, spill width and save block. -/
def opResolvesB (F W Q : Nat) (n : String) : Bool :=
  isGpName n || (spillQsaveOff F W n Q).isSome || (parseMemNameGp n).isSome

theorem opResolvesB_iff {F W Q : Nat} {n : String} :
    opResolvesB F W Q n = true ↔ OpResolves F W Q n := by
  simp [opResolvesB, OpResolves, or_assoc]

/-- The decision of the register moves of `LegalForm` at the x86 encoder. -/
def x86MovB (c : Nat × Nat × Nat) : LinstrR → Bool
  | .Lopn [.reg d] mn [.reg s] =>
      isMovMnem mn && opResolvesB c.1 c.2.1 c.2.2 d && opResolvesB c.1 c.2.1 c.2.2 s &&
        !(encMemName d && encMemName s)
  | _ => false

/-- The decision of the selects of `LegalForm` at the x86 encoder. -/
def x86SelectB : LinstrR → Bool
  | .Lopn [.reg dn] m [.reg cn, .reg tn, .reg fn] =>
      m == withWidthTag 64 "CMOV" && isGpName dn && isGpName cn && isGpName tn && isGpName fn
  | _ => false

/-- The decision of the materialised comparisons of `LegalForm` at the x86 encoder. -/
def x86SetccB : LinstrR → Bool
  | .Lopn [.reg dn] opn [.reg an, .reg sn] =>
      isSetccEncMnem opn && isGpName dn && isGpName an && isGpName sn
  | _ => false

/-- The decision of the materialised comparisons against an immediate of `LegalForm` at the
    x86 encoder. -/
def x86SetccImmB : LinstrR → Bool
  | .Lopn [.reg dn] opn [.reg an, .imm v] => isSetccImmEnc opn v && isGpName dn && isGpName an
  | _ => false

/-- The decision of the immediate moves of `LegalForm` at the x86 encoder. -/
def x86MovImmB (c : Nat × Nat × Nat) : LinstrR → Bool
  | .Lopn [.reg dn] mn [.imm v] =>
      isMovMnem mn &&
        (isGpName dn || ((spillQsaveOff c.1 c.2.1 dn c.2.2).isSome && x86SlotImm mn v))
  | _ => false

/-- The decision of the two-address operations over registers of `LegalForm` at the x86
    encoder. -/
def x86AluB : LinstrR → Bool
  | .Lopn [.reg dn] opn [.reg an, .reg sn] =>
      x86Alu opn && an == dn && isGpName dn && isGpName sn
  | _ => false

/-- The decision of the two-address operations against an immediate of `LegalForm` at the
    x86 encoder. -/
def x86AluImmB : LinstrR → Bool
  | .Lopn [.reg dn] opn [.reg an, .imm v] => x86AluImm opn v && an == dn && isGpName dn
  | _ => false

/-- The decision of the three-register shifts of `LegalForm` at the x86 encoder. -/
def x86ShiftRegB : LinstrR → Bool
  | .Lopn [.reg dn] opn [.reg an, .reg sn] =>
      x86ShiftReg opn && isGpName dn && isGpName an && isGpName sn
  | _ => false

/-- The decision of the one-source register operations of `LegalForm` at the x86 encoder. -/
def x86UnaryB : LinstrR → Bool
  | .Lopn [.reg dn] opn [.reg sn] => x86Unary opn && isGpName dn && isGpName sn
  | _ => false

/-- The decision of the loads and stores of `LegalForm` at the x86 encoder. -/
def x86MemMovB (c : Nat × Nat × Nat) : LinstrR → Bool
  | .Lopn [.reg d] mn [.reg s] =>
      x86MemMov mn && opResolvesB c.1 c.2.1 c.2.2 d && opResolvesB c.1 c.2.1 c.2.2 s &&
        !(encMemName d && encMemName s)
  | _ => false

/-- The decision of the register-indexed loads and address computations of `LegalForm` at
    the x86 encoder. -/
def x86SibLoadB : LinstrR → Bool
  | .Lopn [.reg dn] opn [.arrIdx bn xn sc] =>
      x86SibLoad opn xn sc && isGpName dn && isGpName bn && isGpName xn
  | _ => false

/-- The decision of the register-indexed stores of `LegalForm` at the x86 encoder. -/
def x86SibStoreB : LinstrR → Bool
  | .Lopn [_] opn [.arrIdx bn xn sc, .reg vn] =>
      x86SibStore opn sc && isGpName bn && isGpName xn && isGpName vn
  | _ => false

/-- The decision of the three-source carry-chain additions of `LegalForm` at the x86
    encoder. -/
def x86Carry3B : LinstrR → Bool
  | .Lopn [.reg dn] opn [.reg an, .reg sn, .reg kn] =>
      x86Carry3 opn && isGpName dn && isGpName an && isGpName sn && isGpName kn
  | _ => false

/-- The decision of the flag materialisations of `LegalForm` at the x86 encoder. -/
def x86FlagOutB : LinstrR → Bool
  | .Lopn [.reg dn] opn srcs => x86FlagOut opn srcs && isGpName dn
  | _ => false

/-- The decision of the widening multiplications of `LegalForm` at the x86 encoder. -/
def x86WideMulB : LinstrR → Bool
  | .Lopn [.reg ln, .reg hn] opn [.reg sn] =>
      x86WideMul opn && isGpName ln && isGpName hn && isGpName sn
  | _ => false

/-- The decision of the constant-index stack-array stores of `LegalForm` at the x86
    encoder. -/
def x86StoreImmB : LinstrR → Bool
  | .Lopn [_] opn [.reg bn, .reg vn, .imm k] =>
      opn == "STOREIMM" && x86StoreImm k && isGpName bn && isGpName vn
  | _ => false

/-- The decision of the stack-array zeroings of `LegalForm` at the x86 encoder: into a
    destination register, and from a base register with no destination. -/
def x86ZeroArrB : LinstrR → Bool
  | .Lopn [.reg dn] opn [.imm n, .imm w] => opn == "ZEROARR" && x86ZeroArr n w && isGpName dn
  | .Lopn [] opn [.reg bn, .imm n, .imm w] => opn == "ZEROARR" && x86ZeroArr n w && isGpName bn
  | _ => false

/-- **The legal forms of the x86 encoder** in the context `c`, as a decision: the disjunction
    of the decisions of the families of `LegalForm`. -/
def x86LegalB (c : Nat × Nat × Nat) (i : LinstrR) : Bool :=
  x86MovB c i || x86SelectB i || x86SetccB i || x86SetccImmB i || x86MovImmB c i ||
    x86AluB i || x86AluImmB i || x86ShiftRegB i || x86UnaryB i || x86MemMovB c i ||
    x86SibLoadB i || x86SibStoreB i || x86Carry3B i || x86FlagOutB i || x86WideMulB i ||
    x86Fixed i || x86StoreImmB i || x86ZeroArrB i

/-- A decision of a family of `x86LegalB` gives a legal form. -/
theorem legalForm_of_x86LegalB {c : Nat × Nat × Nat} {i : LinstrR} (h : x86LegalB c i = true) :
    LegalForm X86Isa.x86Isa x86Enc c i := by
  simp only [x86LegalB, Bool.or_eq_true] at h
  rcases h with ((((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) |
    h) | h) | h) | h) | h
  rotate_left 15
  · exact .fixed i h
  · unfold x86StoreImmB at h; split at h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨rfl, ho⟩, h1⟩, h2⟩ := h
      exact .storeImm _ _ _ _ ho h1 h2
    · cases h
  · unfold x86ZeroArrB at h; split at h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, ho⟩, h1⟩ := h
      exact .zeroArr _ _ _ ho h1
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, ho⟩, h1⟩ := h
      exact .zeroArrSrc _ _ _ ho h1
    · cases h
  · unfold x86MovB at h; split at h
    · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨⟨⟨hm, hd⟩, hs⟩, hds⟩ := h
      exact .mov _ _ _ hm (opResolvesB_iff.1 hd) (opResolvesB_iff.1 hs) hds
    · cases h
  · unfold x86SelectB at h; split at h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨rfl, h1⟩, h2⟩, h3⟩, h4⟩ := h
      exact .select "CMOV" _ _ _ _ rfl h1 h2 h3 h4
    · cases h
  · unfold x86SetccB at h; split at h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨ho, h1⟩, h2⟩, h3⟩ := h
      exact .setcc _ _ _ _ ho h1 h2 h3
    · cases h
  · unfold x86SetccImmB at h; split at h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨ho, h1⟩, h2⟩ := h
      exact .setccImm _ _ _ _ ho h1 h2
    · cases h
  · unfold x86MovImmB at h; split at h
    · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨hm, hd | ⟨hs, hv⟩⟩ := h
      · exact .movImmReg _ _ _ hm hd
      · exact .movImmSlot _ _ _ hm hs hv
    · cases h
  · unfold x86AluB at h; split at h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨ho, rfl⟩, h1⟩, h2⟩ := h
      exact .alu _ _ _ ho h1 h2
    · cases h
  · unfold x86AluImmB at h; split at h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨ho, rfl⟩, h1⟩ := h
      exact .aluImm _ _ _ ho h1
    · cases h
  · unfold x86ShiftRegB at h; split at h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨ho, h1⟩, h2⟩, h3⟩ := h
      exact .shiftReg _ _ _ _ ho h1 h2 h3
    · cases h
  · unfold x86UnaryB at h; split at h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨ho, h1⟩, h2⟩ := h
      exact .unary _ _ _ ho h1 h2
    · cases h
  · unfold x86MemMovB at h; split at h
    · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨⟨⟨hm, hd⟩, hs⟩, hds⟩ := h
      exact .memMov _ _ _ hm (opResolvesB_iff.1 hd) (opResolvesB_iff.1 hs) hds
    · cases h
  · unfold x86SibLoadB at h; split at h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨ho, h1⟩, h2⟩, h3⟩ := h
      exact .sibLoad _ _ _ _ _ ho h1 h2 h3
    · cases h
  · unfold x86SibStoreB at h; split at h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨ho, h1⟩, h2⟩, h3⟩ := h
      exact .sibStore _ _ _ _ _ _ ho h1 h2 h3
    · cases h
  · unfold x86Carry3B at h; split at h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨ho, h1⟩, h2⟩, h3⟩, h4⟩ := h
      exact .carry3 _ _ _ _ _ ho h1 h2 h3 h4
    · cases h
  · unfold x86FlagOutB at h; split at h
    · simp only [Bool.and_eq_true] at h
      exact .flagOut _ _ _ h.1 h.2
    · cases h
  · unfold x86WideMulB at h; split at h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨ho, h1⟩, h2⟩, h3⟩ := h
      exact .wideMul _ _ _ _ ho h1 h2 h3
    · cases h

/-- A legal form is decided by `x86LegalB`. -/
theorem x86LegalB_of_legalForm {c : Nat × Nat × Nat} {i : LinstrR}
    (h : LegalForm X86Isa.x86Isa x86Enc c i) : x86LegalB c i = true := by
  simp only [x86LegalB, Bool.or_eq_true]
  cases h with
  | mov mn d s hm hd hs hds =>
    have hd' := opResolvesB_iff.2 hd
    have hs' := opResolvesB_iff.2 hs
    change (encMemName d && encMemName s) = false at hds
    simp [x86MovB, hm, hd', hs', hds]
  | select m dn cn tn fn hsel h1 h2 h3 h4 =>
    have hm : m = "CMOV" := (Option.some.inj hsel).symm
    subst hm
    change isGpName dn = true at h1
    change isGpName cn = true at h2
    change isGpName tn = true at h3
    change isGpName fn = true at h4
    simp [x86SelectB, h1, h2, h3, h4]
  | setcc opn dn an sn ho h1 h2 h3 =>
    change isSetccEncMnem opn = true at ho
    change isGpName dn = true at h1
    change isGpName an = true at h2
    change isGpName sn = true at h3
    simp [x86SetccB, ho, h1, h2, h3]
  | setccImm opn dn an v ho h1 h2 =>
    change isSetccImmEnc opn v = true at ho
    change isGpName dn = true at h1
    change isGpName an = true at h2
    simp [x86SetccImmB, ho, h1, h2]
  | movImmReg mn dn v hm h1 =>
    change isGpName dn = true at h1
    simp [x86MovImmB, hm, h1]
  | movImmSlot mn dn v hm h1 h2 =>
    change (spillQsaveOff c.1 c.2.1 dn c.2.2).isSome = true at h1
    change x86SlotImm mn v = true at h2
    simp [x86MovImmB, hm, h1, h2]
  | alu opn dn sn ho h1 h2 =>
    change x86Alu opn = true at ho
    change isGpName dn = true at h1
    change isGpName sn = true at h2
    simp [x86AluB, ho, h1, h2]
  | aluImm opn dn v ho h1 =>
    change x86AluImm opn v = true at ho
    change isGpName dn = true at h1
    simp [x86AluImmB, ho, h1]
  | shiftReg opn dn an sn ho h1 h2 h3 =>
    change x86ShiftReg opn = true at ho
    change isGpName dn = true at h1
    change isGpName an = true at h2
    change isGpName sn = true at h3
    simp [x86ShiftRegB, ho, h1, h2, h3]
  | unary opn dn sn ho h1 h2 =>
    change x86Unary opn = true at ho
    change isGpName dn = true at h1
    change isGpName sn = true at h2
    simp [x86UnaryB, ho, h1, h2]
  | memMov mn d s hm hd hs hds =>
    change x86MemMov mn = true at hm
    have hd' := opResolvesB_iff.2 hd
    have hs' := opResolvesB_iff.2 hs
    change (encMemName d && encMemName s) = false at hds
    simp [x86MemMovB, hm, hd', hs', hds]
  | sibLoad opn dn bn xn sc ho h1 h2 h3 =>
    change x86SibLoad opn xn sc = true at ho
    change isGpName dn = true at h1
    change isGpName bn = true at h2
    change isGpName xn = true at h3
    simp [x86SibLoadB, ho, h1, h2, h3]
  | sibStore a opn bn xn vn sc ho h1 h2 h3 =>
    change x86SibStore opn sc = true at ho
    change isGpName bn = true at h1
    change isGpName xn = true at h2
    change isGpName vn = true at h3
    simp [x86SibStoreB, ho, h1, h2, h3]
  | carry3 opn dn an sn kn ho h1 h2 h3 h4 =>
    change x86Carry3 opn = true at ho
    change isGpName dn = true at h1
    change isGpName an = true at h2
    change isGpName sn = true at h3
    change isGpName kn = true at h4
    simp [x86Carry3B, ho, h1, h2, h3, h4]
  | flagOut opn dn srcs ho h1 =>
    change x86FlagOut opn srcs = true at ho
    change isGpName dn = true at h1
    simp [x86FlagOutB, ho, h1]
  | wideMul opn ln hn sn ho h1 h2 h3 =>
    change x86WideMul opn = true at ho
    change isGpName ln = true at h1
    change isGpName hn = true at h2
    change isGpName sn = true at h3
    simp [x86WideMulB, ho, h1, h2, h3]
  | storeImm a bn vn k ho h1 h2 =>
    change x86StoreImm k = true at ho
    change isGpName bn = true at h1
    change isGpName vn = true at h2
    simp [x86StoreImmB, ho, h1, h2]
  | zeroArr dn n w ho h1 =>
    change x86ZeroArr n w = true at ho
    change isGpName dn = true at h1
    simp [x86ZeroArrB, ho, h1]
  | zeroArrSrc bn n w ho h1 =>
    change x86ZeroArr n w = true at ho
    change isGpName bn = true at h1
    simp [x86ZeroArrB, ho, h1]
  | fixed i hi =>
    change x86Fixed i = true at hi
    simp [hi]

/-- **`x86LegalB` decides the legal forms** `LegalForm` of the x86 instruction set at the x86
    encoder. -/
theorem x86LegalB_iff {c : Nat × Nat × Nat} {i : LinstrR} :
    x86LegalB c i = true ↔ LegalForm X86Isa.x86Isa x86Enc c i :=
  ⟨legalForm_of_x86LegalB, x86LegalB_of_legalForm⟩

/-- **The x86 back end**: the machine `x86Mach` and the assembly simulation `x86AsmSim` of
    the class `printedAddrWB` at the regime `doitm`, on the address semantics of printed
    bodies; the legal forms `LegalForm` of the x86 encoder in the context of the body,
    decided by `x86LegalB`; the encodability `encodableLcmd`; a callee as its symbol and
    code, the checks `x86LinkB`, and the byte length of the function of the caller as call
    distance. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.x86Backend :
    VIR.LprogIsa.IsaBackend X86Isa.x86Isa where
  M := X86Isa.x86Mach .doitm
  src := X86AsmSim.x86AddrSem DecodePrintedAddrW.SafeW
  toBody := id
  asm := X86AsmSim.x86AsmSim .doitm
  legal := fun body i => x86LegalB (x86Enc.ctx body) i
  encodable := encodableLcmd
  Callee := String × List (BitVec 8)
  link := fun c b => VIR.LprogIsa.x86LinkB c.1 c.2 b
  callDist := fun c b => (encodeLfundefBytesReloc (VIR.LprogIsa.x86LinkSym c.1 b) b).length

theorem _root_.CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.x86Backend_asm :
    VIR.LprogIsa.x86Backend.asm = X86AsmSim.x86AsmSim .doitm := rfl

theorem _root_.CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.x86Backend_encodable :
    VIR.LprogIsa.x86Backend.encodable = encodableLcmd := rfl

/-- **An instruction of a body is legal at the x86 back end exactly when it has a legal form**
    of the x86 encoder in the context of the body. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.x86Backend_legal
    (body : Lcmd) (i : LinstrR) :
    VIR.LprogIsa.x86Backend.legal body i = true ↔
      LegalForm X86Isa.x86Isa x86Enc (x86Enc.ctx body) i :=
  x86LegalB_iff

/-- An operand is allocated at a frame size, spill width and save block exactly when it is
    an allocated operand of the x86 encoder in that context. -/
theorem allocOp_iff_allocOpI {F W Q : Nat} {o : LOperand} :
    AllocOp F W Q o ↔ AllocOpI x86Enc (F, W, Q) o := by
  simp only [AllocOp, AllocOpI, x86Enc, isSpill_reg]

/-- **The x86 encoder is complete for the x86 back end.** -/
theorem x86Enc_complete : EncoderComplete VIR.LprogIsa.x86Backend x86Enc where
  encodable_eq _ := rfl
  pool_reg := by decide +kernel
  reload_reg := by decide +kernel
  reloadSnd_reg := by decide +kernel
  reg_resolves _ _ h := Or.inl h
  slot_resolves _ _ h := Or.inr (Or.inl h)
  reg_not_spill n h := by
    rw [isSpill_reg]
    cases hk : hasPrefix n "k."
    · rfl
    · change isGpName n = true at h
      rw [isGpName_of_hasPrefix_k hk] at h; cases h
  reg_not_mem _ h := encMemName_of_isGpName h
  spill_mem n h := by
    rw [isSpill_reg] at h
    simp [x86Enc, encMemName, isSpillOrQsave_of_k h]
  mem_loadCSE _ h := isMemName_of_encMemName h
  mov_iff c mn d s hm := by
    refine (encodableLinstrR_mov_iff hm).trans ⟨fun h => ?_, fun ⟨hd, hs, hds⟩ =>
      encTwoAddr_ne_nil hd hs hds⟩
    obtain ⟨hd, hs⟩ := opResolves_of_encTwoAddr h
    refine ⟨hd, hs, ?_⟩
    rcases encTwoAddr_ne_nil_iff.1 h with ⟨hg, -⟩ | ⟨-, hg⟩
    · show (encMemName d && encMemName s) = false
      simp [encMemName_of_isGpName hg]
    · show (encMemName d && encMemName s) = false
      simp [encMemName_of_isGpName hg]
  select_reg m hm c dn cn tn fn hd hc ht hf := by
    have hm' : m = "CMOV" := (Option.some.inj hm).symm
    subst hm'
    exact encodableLinstrR_cmov64_gp hd hc ht hf
  setcc_reg c opn dn an sn ho hd ha hs := encodableLinstrR_setcc_gp ho hd ha hs
  setccImm_reg c opn dn an v ho hd ha := encodableLinstrR_setccImm_gp ho hd ha
  movImm_reg _ _ _ _ hm hd := encodableLinstrR_movImm_gp hm hd
  movImm_slot _ _ _ _ hm hd hv := encodableLinstrR_movImm_slot hm hd hv
  alu_reg _ _ _ _ ho hd hs := encodableLinstrR_alu ho hd hs
  alu_imm _ _ _ _ ho hd := encodableLinstrR_aluImm ho hd
  shift_reg _ _ _ _ _ ho hd ha hs := encodableLinstrR_shiftReg ho hd ha hs
  unary_reg _ _ _ _ ho hd hs := encodableLinstrR_unary ho hd hs
  memMov_res _ _ _ _ hm hd hs hds := encodableLinstrR_memMov hm hd hs hds
  sibLoad_reg _ _ _ _ _ _ ho hd hb hx := encodableLinstrR_sibLoad ho hd hb hx
  sibStore_reg _ _ _ _ _ _ _ ho hb hx hv := encodableLinstrR_sibStore ho hb hx hv
  carry3_reg _ _ _ _ _ _ ho hd ha hs hk := encodableLinstrR_carry3 ho hd ha hs hk
  flagOut_reg _ _ _ _ ho hd := encodableLinstrR_flagOut ho hd
  wideMul_reg _ _ _ _ _ ho hl hh hs := encodableLinstrR_wideMul ho hl hh hs
  storeImm_reg _ _ _ _ _ ho hb hv := encodableLinstrR_storeImm ho hb hv
  zeroArr_reg _ _ _ _ ho hd := encodableLinstrR_zeroArr ho hd
  zeroArrSrc_reg _ _ _ _ ho hb := encodableLinstrR_zeroArrSrc ho hb
  fixed_instr _ _ hi := encodableLinstrR_fixed hi

/-- The select mnemonic of the x86 instruction set is `CMOV`. -/
theorem x86Isa_selectMnemonic : X86Isa.x86Isa.selectMnemonic = some "CMOV" := rfl

/-! ## The legalised register copy -/

/-- **Every instruction of a legalised register copy over allocated operands is
    encodable.** -/
theorem legalizeMov_encodable {F W Q : Nat} {d s : LOperand} {mov : String}
    (hm : isMovMnem mov = true) (hd : AllocOp F W Q d) (hs : AllocOp F W Q s) :
    ∀ i ∈ legalizeMov d s mov, encodableLinstrR F W i Q = true :=
  x86Enc_complete.legalizeMovI_encodable (c := (F, W, Q)) hm (allocOp_iff_allocOpI.1 hd)
    (allocOp_iff_allocOpI.1 hs)

/-- **Every instruction of the one-source arm of the allocation on a register move
    over allocated operands is encodable.** -/
theorem legalizeOneSrc_encodable {F W Q : Nat} {u64 : Bool} {opn : String} {d s : LOperand}
    (hm : isMovMnem opn = true) (hd : AllocOp F W Q d) (hs : AllocOp F W Q s) :
    ∀ i ∈ legalizeOneSrc u64 opn d s, encodableLinstrR F W i Q = true :=
  x86Enc_complete.legalizeOneSrcI_encodable (c := (F, W, Q)) hm (allocOp_iff_allocOpI.1 hd)
    (allocOp_iff_allocOpI.1 hs)

/-! ## The scratch select -/

/-- **Every instruction of the scratch select is encodable** when the destination and
    the condition are allocated and the selected values are general-purpose
    registers. -/
theorem cmovSpillSeq_encodable {F W Q : Nat} {d c : LOperand} {tn fn : String}
    (hd : AllocOp F W Q d) (hc : AllocOp F W Q c) (ht : isGpName tn = true)
    (hf : isGpName fn = true) :
    ∀ i ∈ cmovSpillSeq "CMOV:64" d c (.reg tn) (.reg fn), encodableLinstrR F W i Q = true :=
  x86Enc_complete.cmovSpillSeqI_encodable (c := (F, W, Q)) x86Isa_selectMnemonic
    (allocOp_iff_allocOpI.1 hd)
    (allocOp_iff_allocOpI.1 hc) ht hf

/-! ## The scratch comparison -/

/-- **Every instruction of the scratch comparison is encodable** for the comparisons
    `SETE` and `SETNE` over allocated operands. -/
theorem setccSpill?_encodable {F W Q : Nat} {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} {l : List LinstrR} (h : setccSpill? dsts opn srcs = some l)
    (ho : isSetccEncMnem opn = true) (hd : ∀ o ∈ dsts, AllocOp F W Q o)
    (hs : ∀ o ∈ srcs, AllocOp F W Q o) :
    ∀ i ∈ l, encodableLinstrR F W i Q = true :=
  x86Enc_complete.setccSpillI?_encodable (c := (F, W, Q)) h ho
    (fun o ho => allocOp_iff_allocOpI.1 (hd o ho)) (fun o ho => allocOp_iff_allocOpI.1 (hs o ho))

/-! ## The spill legalisation of a general instruction -/

/-- **Every instruction of `legalizeSpillDst` is encodable**, for allocated operands:
    the scratch select when its selected values are registers, the scratch comparison
    when it is `SETE` or `SETNE`, and the single instruction when it is itself
    encodable. -/
theorem legalizeSpillDst_encodable {F W Q : Nat} {dsts : List LOperand} {opn : String}
    {srcs : List LOperand}
    (hd : ∀ o ∈ dsts, AllocOp F W Q o) (hs : ∀ o ∈ srcs, AllocOp F W Q o)
    (hsel : ∀ c t f, srcs = [c, t, f] → opn = "CMOV:64" →
      ∃ tn fn, t = .reg tn ∧ f = .reg fn ∧ isGpName tn = true ∧ isGpName fn = true)
    (hcmp : isSetccMnem opn = true → isSetccEncMnem opn = true)
    (hone : cmovSpillDst? dsts opn srcs = none → setccSpill? dsts opn srcs = none →
      encodableLinstrR F W (.Lopn dsts opn srcs) Q = true) :
    ∀ i ∈ legalizeSpillDst dsts opn srcs, encodableLinstrR F W i Q = true :=
  x86Enc_complete.legalizeSpillDstI_encodable (c := (F, W, Q)) x86Isa_selectMnemonic
    (fun o ho => allocOp_iff_allocOpI.1 (hd o ho)) (fun o ho => allocOp_iff_allocOpI.1 (hs o ho))
    hsel hcmp hone

/-! ## Load forwarding -/

section LoadCSE

open CatCrypt.Crypto.Optimizer.LoadCSE

/-- **One forwarding step keeps an encodable instruction encodable** and the
    environment resolving. -/
theorem stepLoad_encodable {F W Q : Nat} (h : LoadEnv) (i : Linstr) (hh : EnvResolves F W Q h)
    (hi : encodableLinstrR F W i.li_i Q = true) :
    encodableLinstrR F W (stepLoad h i).1.li_i Q = true ∧
      EnvResolves F W Q (stepLoad h i).2 :=
  x86Enc_complete.stepLoad_encodableI (c := (F, W, Q)) h i hh hi

/-- **`loadCSE` preserves encodability**: at a fixed frame size, spill width and save
    block, a body of encodable instructions is forwarded to a body of encodable
    instructions. -/
theorem loadCSE_encodable {F W Q : Nat} (body : List Linstr)
    (hb : ∀ i ∈ body, encodableLinstrR F W i.li_i Q = true) :
    ∀ i ∈ loadCSE body, encodableLinstrR F W i.li_i Q = true :=
  x86Enc_complete.loadCSE_encodableI (c := (F, W, Q)) body hb

/-- **A body whose instructions have legal forms is encodable** at the x86 back end, in the
    context of the body under the x86 encoder. -/
theorem encodable_of_legal_x86 {body : Lcmd}
    (hb : ∀ i ∈ body, LegalForm X86Isa.x86Isa x86Enc (x86Enc.ctx body) i.li_i) :
    encodableLcmd body = true :=
  x86Enc_complete.encodable_of_legal hb

/-- **The legalised body after load forwarding is encodable** at the x86 back end: a body of
    instructions with legal forms in the x86 context of its forwarded body is forwarded by
    `loadCSE` to a body accepted by `encodableLcmd`. -/
theorem encodable_of_legalized_x86 (body : List Linstr)
    (hb : ∀ i ∈ body, LegalForm X86Isa.x86Isa x86Enc (x86Enc.ctx (loadCSE body)) i.li_i) :
    encodableLcmd (loadCSE body) = true :=
  x86Enc_complete.encodable_of_legalized body hb

/-- **The encodability law of the x86 back end**: a body whose instructions are legal at
    `x86Backend` is encodable (the field `IsaBackend.Laws.encodable_of_legal`). -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.x86Backend_encodable_of_legal
    (body : Lcmd) (hb : ∀ i ∈ body, VIR.LprogIsa.x86Backend.legal body i.li_i = true) :
    VIR.LprogIsa.x86Backend.encodable body = true :=
  encodable_of_legal_x86 fun i hi => x86LegalB_iff.1 (hb i hi)

end LoadCSE

end CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeComplete
